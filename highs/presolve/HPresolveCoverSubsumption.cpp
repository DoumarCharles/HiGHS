/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
/*                                                                       */
/*    This file is part of the HiGHS linear optimization suite           */
/*                                                                       */
/*    Available as open-source under the MIT License                     */
/*                                                                       */
/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
/**@file presolve/HPresolveCoverSubsumption.cpp
 * @brief Remove covering rows implied by a smaller covering row (research,
 * option presolve_cover_subsumption).
 *
 * A covering row is sum_{j in S} x_j >= 1 over binary columns (stored with
 * all coefficients v > 0 and lower bound v, or all v < 0 and upper bound v).
 * If S_r is a subset of S_s, row r implies row s, so s is redundant. Removing
 * it leaves columns that were only kept by s free to be dominated.
 */
#include <algorithm>

#include "presolve/HPresolve.h"
#include "presolve/HPresolveUtils.h"

namespace presolve {

HPresolve::Result HPresolve::coverSubsumption(
    HighsPostsolveStack& postsolve_stack) {
  const double t0 = timer ? timer->read() : 0.0;
  // nothing deleted since the last call: nothing new to find
  const HighsInt deletions = numDeletedRows + numDeletedCols;
  if (deletions == coverLastDeletions) return Result::kOk;
  coverLastDeletions = deletions;

  // covering rows with their sorted columns
  std::vector<HighsInt> cover;
  std::vector<HighsInt> start(1, 0);
  std::vector<HighsInt> cols;
  for (HighsInt row = 0; row < model->num_row_; ++row) {
    if (rowDeleted[row] || rowsize[row] < 2) continue;
    // a covering row has one infinite side and a nonzero finite side
    const bool lowerSide = model->row_upper_[row] == kHighsInf &&
                           model->row_lower_[row] > 0;
    const bool upperSide = model->row_lower_[row] == -kHighsInf &&
                           model->row_upper_[row] < 0;
    if (!lowerSide && !upperSide) continue;
    double v = 0.0;
    bool ok = true;
    const size_t mark = cols.size();
    for (const HighsSliceNonzero& nz : getRowVector(row)) {
      if (!isBinary(nz.index()) || (v != 0.0 && nz.value() != v)) {
        ok = false;
        break;
      }
      v = nz.value();
      cols.push_back(nz.index());
    }
    if (ok)
      ok = v > 0 ? model->row_lower_[row] == v &&
                       model->row_upper_[row] == kHighsInf
                 : model->row_upper_[row] == v &&
                       model->row_lower_[row] == -kHighsInf;
    if (!ok) {
      cols.resize(mark);
      continue;
    }
    std::sort(cols.begin() + mark, cols.end());
    cover.push_back(row);
    start.push_back(static_cast<HighsInt>(cols.size()));
  }
  if (cover.size() < 2) return Result::kOk;

  // covering rows of each column, and a 64-bit signature of each row
  const HighsInt numCover = static_cast<HighsInt>(cover.size());
  std::vector<HighsInt> colStart(model->num_col_ + 1, 0);
  std::vector<HighsInt> colList(cols.size());
  std::vector<uint64_t> sig(numCover, 0);
  for (HighsInt col : cols) colStart[col + 1]++;
  for (HighsInt col = 0; col < model->num_col_; ++col)
    colStart[col + 1] += colStart[col];
  {
    std::vector<HighsInt> next(colStart.begin(), colStart.end() - 1);
    for (HighsInt c = 0; c < numCover; ++c)
      for (HighsInt p = start[c]; p < start[c + 1]; ++p) {
        sig[c] |= uint64_t{1}
                  << ((uint64_t(cols[p]) * 0x9E3779B97F4A7C15ull) >> 58);
        colList[next[cols[p]]++] = c;
      }
  }
  auto numColRows = [&](HighsInt col) {
    return colStart[col + 1] - colStart[col];
  };

  std::vector<HighsInt> order(numCover);
  for (HighsInt c = 0; c < numCover; ++c) order[c] = c;
  auto size = [&](HighsInt c) { return start[c + 1] - start[c]; };
  std::sort(order.begin(), order.end(), [&](HighsInt a, HighsInt b) {
    return std::make_pair(size(a), a) < std::make_pair(size(b), b);
  });

  // work: candidate rows looked at plus binary searches; capped
  const size_t maxWork = 20 * cols.size() + 100000;
  size_t work = 0;
  HighsInt numVisited = 0;
  HighsInt numRemoved = 0;
  std::vector<char> removed(numCover, 0);
  for (HighsInt r : order) {
    if (removed[r]) continue;
    if (work > maxWork) break;
    if ((++numVisited & 63) == 0) HPRESOLVE_CHECKED_CALL(checkTimeLimit());
    // candidates: covering rows of the column of r in the fewest of them
    HighsInt best = cols[start[r]];
    for (HighsInt p = start[r] + 1; p < start[r + 1]; ++p)
      if (numColRows(cols[p]) < numColRows(best)) best = cols[p];
    work += numColRows(best);
    for (HighsInt q = colStart[best]; q < colStart[best + 1]; ++q) {
      const HighsInt s = colList[q];
      if (s == r || removed[s] || size(s) < size(r)) continue;
      if ((sig[r] & ~sig[s]) != 0) continue;
      // equal rows: keep the one sorted first
      if (size(s) == size(r) && s < r) continue;
      // every column of r in s (binary search, stop at the first miss)
      const HighsInt* sb = cols.data() + start[s];
      const HighsInt* se = cols.data() + start[s + 1];
      bool contained = true;
      for (HighsInt p = start[r]; p < start[r + 1]; ++p) {
        ++work;
        if (!std::binary_search(sb, se, cols[p])) {
          contained = false;
          break;
        }
      }
      if (!contained) continue;
      removed[s] = 1;
      postsolve_stack.redundantRow(cover[s]);
      removeRow(cover[s]);
      numRemoved++;
      HPRESOLVE_CHECKED_CALL(checkLimits(postsolve_stack));
    }
  }

  // the rows removed here do not call for another search
  coverLastDeletions = numDeletedRows + numDeletedCols;
  if (numRemoved > 0 && options->presolve_cover_trigger)
    domcolCountPossible = true;
  if (numRemoved > 0)
    highsLogDev(options->log_options, HighsLogType::kInfo,
                "Removed %" HIGHSINT_FORMAT " subsumed covering rows\n",
                numRemoved);
  highsLogDev(options->log_options, HighsLogType::kVerbose,
              "Cover subsumption: %d covering rows, %d removed, work %.0f, "
              "%.3f s\n",
              static_cast<int>(numCover), static_cast<int>(numRemoved),
              static_cast<double>(work), (timer ? timer->read() : 0.0) - t0);
  return Result::kOk;
}

}  // namespace presolve
