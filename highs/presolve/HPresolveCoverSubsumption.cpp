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
  auto isCoverRow = [&](HighsInt row) {
    if (rowDeleted[row] || rowsize[row] < 2) return false;
    double v = 0.0;
    for (const HighsSliceNonzero& nz : getRowVector(row)) {
      if (!isBinary(nz.index())) return false;
      if (v == 0.0)
        v = nz.value();
      else if (nz.value() != v)
        return false;
    }
    if (v > 0)
      return model->row_lower_[row] == v && model->row_upper_[row] == kHighsInf;
    return model->row_upper_[row] == v && model->row_lower_[row] == -kHighsInf;
  };

  std::vector<HighsInt> cover;
  std::vector<uint64_t> sig(model->num_row_, 0);
  std::vector<std::vector<HighsInt>> colRows(model->num_col_);
  for (HighsInt row = 0; row < model->num_row_; ++row) {
    if (!isCoverRow(row)) continue;
    cover.push_back(row);
    for (const HighsSliceNonzero& nz : getRowVector(row)) {
      sig[row] |= uint64_t{1} << (nz.index() & 63);
      colRows[nz.index()].push_back(row);
    }
  }
  if (cover.size() < 2) return Result::kOk;

  std::sort(cover.begin(), cover.end(), [&](HighsInt a, HighsInt b) {
    return std::make_pair(rowsize[a], a) < std::make_pair(rowsize[b], b);
  });

  std::vector<char> mark(model->num_col_, 0);
  HighsInt numRemoved = 0;
  size_t work = 0;
  for (HighsInt r : cover) {
    if (rowDeleted[r]) continue;
    if ((++work & 63) == 0) HPRESOLVE_CHECKED_CALL(checkTimeLimit());
    // candidates: covering rows of the column of r in the fewest of them
    HighsInt best = -1;
    for (const HighsSliceNonzero& nz : getRowVector(r)) {
      mark[nz.index()] = 1;
      if (best == -1 || colRows[nz.index()].size() < colRows[best].size())
        best = nz.index();
    }
    const HighsInt size = rowsize[r];
    for (HighsInt s : colRows[best]) {
      if (s == r || rowDeleted[s] || rowsize[s] < size) continue;
      if ((sig[r] & ~sig[s]) != 0) continue;
      // equal rows: keep the one sorted first
      if (rowsize[s] == size && s < r) continue;
      HighsInt hits = 0;
      for (const HighsSliceNonzero& nz : getRowVector(s))
        hits += mark[nz.index()];
      if (hits < size) continue;
      postsolve_stack.redundantRow(s);
      removeRow(s);
      numRemoved++;
      HPRESOLVE_CHECKED_CALL(checkLimits(postsolve_stack));
    }
    for (const HighsSliceNonzero& nz : getRowVector(r)) mark[nz.index()] = 0;
  }

  if (numRemoved > 0 && options->presolve_cover_trigger)
    domcolCountPossible = true;
  if (numRemoved > 0)
    highsLogDev(options->log_options, HighsLogType::kInfo,
                "Removed %" HIGHSINT_FORMAT " subsumed covering rows\n",
                numRemoved);
  return Result::kOk;
}

}  // namespace presolve
