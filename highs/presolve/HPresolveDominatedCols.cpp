/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
/*                                                                       */
/*    This file is part of the HiGHS linear optimization suite           */
/*                                                                       */
/*    Available as open-source under the MIT License                     */
/*                                                                       */
/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
#include <unordered_set>

#include "mip/HighsMipSolverData.h"
#include "presolve/HPresolve.h"
#include "presolve/HPresolveUtils.h"

namespace presolve {

HPresolve::Result HPresolve::dominatedColumns(
    HighsPostsolveStack& postsolve_stack) {
  const double domcolT0 = timer ? timer->read() : 0.0;
  // See section 6.4 "Dominated columns", Achterberg et al., Presolve Reductions
  // in Mixed Integer Programming, INFORMS Journal on Computing 32(2):473-506.
  // See also Gamrath, G., Koch, T., Martin, A. et al., Progress in presolving
  // for mixed integer programming, Math. Prog. Comp. 7, 367–398 (2015).
  //
  // Given a domination relationship x_j ≻ x_k (Definition 1 in Gamrath
  // et al.), there exists an optimal solution where x_j = u_j or x_k = l_k
  // (Theorem 2). If this can be verified (e.g. via implied bounds or
  // cliques), the dominated variable is fixed. Otherwise, predictive bound
  // analysis (Theorem 3) derives tighter bounds on x_j and x_k by computing
  // implied bounds conditional on the other variable being at its extreme.
  // Worst-case bounds (MINU/MAXU) use the worst-case row activity (maximal
  // for ≤-constraints, minimal for ≥-constraints) to obtain bounds that are
  // feasible independent of other variables' values.

  // non-zero signatures for comparing columns
  std::vector<std::pair<uint32_t, uint32_t>> signatures(model->num_col_);

  // count overall number of domination checks and number of checks performed
  // for predictive bound analysis
  size_t numDomChecks = 0;
  size_t numDomChecksPredBndAnalysis = 0;
  // research (measurement only, dev log): pairs offered / past the skips
  size_t numPairs = 0;
  size_t numPairsChecked = 0;
  size_t pairsDir[2] = {0, 0};
  size_t redsDir[2] = {0, 0};

  auto addSignature = [&](HighsInt row, HighsInt col, uint32_t rowLowerFinite,
                          uint32_t rowUpperFinite) {
    HighsInt rowHashedPos = (HighsHashHelpers::hash(row) >> 59);
    assert(rowHashedPos < 32);
    signatures[col].first |= rowLowerFinite << rowHashedPos;
    signatures[col].second |= rowUpperFinite << rowHashedPos;
  };

  auto checkDominationNonZero = [&](HighsInt row, double aj, double ak) {
    if (isRanged(row)) {
      // the row is an equality or ranged row, therefore the coefficients must
      // be parallel, otherwise one of the inequalities given by the row rules
      // out domination
      if (std::abs(aj - ak) > options->small_matrix_value) return false;
      return true;
    }

    // normalize row to a <= constraint
    if (model->row_upper_[row] == kHighsInf) {
      aj = -aj;
      ak = -ak;
    }

    // the coefficient of the dominating column needs to be smaller than or
    // equal to the coefficient of the dominated column
    if (aj > ak + options->small_matrix_value) return false;
    return true;
  };

  auto checkSignatures = [&](HighsInt scalj, HighsInt j, HighsInt scalk,
                             HighsInt k) {
    uint32_t sjMinus = signatures[j].first;
    uint32_t sjPlus = signatures[j].second;
    if (scalj == -1) std::swap(sjPlus, sjMinus);

    uint32_t skMinus = signatures[k].first;
    uint32_t skPlus = signatures[k].second;
    if (scalk == -1) std::swap(skPlus, skMinus);

    // the set of rows with a negative coefficient must be a superset of the
    // dominated columns set of rows with a negative coefficient
    if ((~sjMinus & skMinus) != 0) return false;

    // the set of rows with a positive coefficient must be a subset of the
    // dominated columns set of rows with a positive coefficient
    if ((sjPlus & ~skPlus) != 0) return false;

    return true;
  };

  auto checkDomination = [&](HighsInt scalj, HighsInt j, HighsInt scalk,
                             HighsInt k) {
    // increment counter
    numDomChecks++;

    // rule out domination from integers to continuous variables
    if (model->integrality_[j] == HighsVarType::kInteger &&
        model->integrality_[k] == HighsVarType::kContinuous)
      return false;

    // check the signatures
    if (!checkSignatures(scalj, j, scalk, k)) return false;

    // the dominating columns cost must be smaller or equal to the dominated
    // columns cost
    if (scalj * model->col_cost_[j] >
        scalk * model->col_cost_[k] + options->small_matrix_value)
      return false;

    // finally check the column vectors
    for (const HighsSliceNonzero& nonz : getColumnVector(j)) {
      HighsInt row = nonz.index();
      HighsInt akPos = findNonzero(row, k);
      if (!checkDominationNonZero(row, scalj * nonz.value(),
                                  scalk * (akPos == -1 ? 0.0 : Avalue[akPos])))
        return false;
    }

    // check row only occurring in the column vector of k
    for (const HighsSliceNonzero& nonz : getColumnVector(k)) {
      HighsInt row = nonz.index();
      HighsInt ajPos = findNonzero(row, j);
      // only rows in which aj does not occur are left to check
      if (ajPos != -1) continue;
      if (!checkDominationNonZero(row, 0.0, scalk * nonz.value())) return false;
    }

    return true;
  };

  for (size_t i = 0; i != Avalue.size(); ++i) {
    if (Avalue[i] == 0) continue;

    HighsInt row = Arow[i];
    HighsInt col = Acol[i];
    bool rowLowerFinite = model->row_lower_[row] != -kHighsInf;
    bool rowUpperFinite = model->row_upper_[row] != kHighsInf;

    if (Avalue[i] > 0)
      addSignature(row, col, rowLowerFinite, rowUpperFinite);
    else
      addSignature(row, col, rowUpperFinite, rowLowerFinite);
  }

  // count number of fixed columns and modified bounds
  HighsInt numCols = 0;
  HighsInt numFixedCols = 0;
  HighsInt numFixedColsPredBndAnalysis = 0;
  HighsInt numModifiedBndsPredBndAnalysis = 0;

  // parameters for predictive bound analysis
  const size_t maxAverageNumDomChecksPredBndAnalysis = 10000;
  const double minAverageNumRedsPredBndAnalysis = 1e-2;

  // perform predictive bound analysis?
  bool allowPredBndAnalysis = true;
  std::vector<HighsInt> check_rowpositions;

  // research (presolve_domcol_row_cache): row positions collected by
  // checkRow, reused until an entry is inserted into the matrix (fixings only
  // delete entries, which checkRow skips)
  const bool rowCache = options->presolve_domcol_row_cache;
  std::vector<std::vector<HighsInt>> cache_rowpositions;
  std::vector<size_t> cache_rowstamp;
  if (rowCache) {
    cache_rowpositions.resize(model->num_row_);
    cache_rowstamp.assign(model->num_row_, ~size_t{0});
  }

  // research (presolve_domcol_mirror_skip): a relation y ≻ z is also listed
  // as -z ≻ -y by the scan of the other column's row of the other sign. A
  // column skips a row with no opposite-sign entry when every entry's mirror
  // row is strictly shorter (ties: the lower index scans) and no entry left
  // its mirror unscanned; a skipped row forces the mirror scans, which then
  // try both fixings of Theorem 2.
  const bool fvs = options->presolve_domcol_first_visit;
  const bool mirrorSkip = options->presolve_domcol_mirror_skip &&
                          !options->presolve_domcol_pair_once && !fvs;
  // sign of an entry in <= form: 1 = positive ("plus" row), 0 = negative
  auto entrySign = [&](HighsInt row, double val) -> HighsInt {
    return (model->row_upper_[row] != kHighsInf ? val : -val) > 0 ? 1 : 0;
  };
  // per column and sign: length of its shortest row of that sign (snapshot)
  std::vector<HighsInt> mirrorLen;
  // per visited column: bit q = its row of sign q was not scanned, bit 2 + q
  // = that scan was skipped by this rule
  std::vector<uint8_t> scanFlags;
  struct MirrorRowStats {
    HighsInt count[2];
    HighsInt notScanned[2];
    HighsInt skipped[2];
    HighsInt maxMirror[2];
    HighsInt maxMirrorCol[2];
    HighsInt notScannedCol[2];
    size_t stamp;
  };
  std::vector<MirrorRowStats> mirrorRows;
  std::vector<HighsInt> mirror_rowpositions;
  size_t numMirrorSkipped[2] = {0, 0};
  size_t numMirrorForced = 0;
  size_t numMirrorFixCol = 0;
  size_t numMirrorRecomputed = 0;
  if (mirrorSkip) {
    mirrorLen.assign(2 * static_cast<size_t>(model->num_col_), kHighsIInf);
    scanFlags.assign(model->num_col_, 0);
    for (HighsInt c = 0; c < model->num_col_; ++c) {
      if (colDeleted[c]) continue;
      for (const HighsSliceNonzero& nonz : getColumnVector(c)) {
        HighsInt q = entrySign(nonz.index(), nonz.value());
        mirrorLen[2 * c + q] =
            std::min(mirrorLen[2 * c + q], rowsize[nonz.index()]);
      }
    }
    MirrorRowStats init = {};
    init.stamp = ~size_t{0};
    mirrorRows.assign(model->num_row_, init);
  }
  // per row and sign q: entries, entries whose row of sign 1 - q was not
  // scanned / was skipped, largest mirror length; recomputed after a matrix
  // insertion, updated when a column is visited (deletions keep upper bounds)
  auto mirrorStats = [&](HighsInt row) -> const MirrorRowStats& {
    MirrorRowStats& st = mirrorRows[row];
    if (st.stamp == numMatrixLinks) return st;
    st = MirrorRowStats();
    st.maxMirror[0] = st.maxMirror[1] = -1;
    st.maxMirrorCol[0] = st.maxMirrorCol[1] = -1;
    getRowPositions(row, mirror_rowpositions);
    for (HighsInt pos : mirror_rowpositions) {
      if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
      HighsInt c = Acol[pos];
      if (colDeleted[c]) continue;
      HighsInt q = entrySign(row, Avalue[pos]);
      st.count[q]++;
      HighsInt m = mirrorLen[2 * c + 1 - q];
      if (m > st.maxMirror[q] ||
          (m == st.maxMirror[q] && c > st.maxMirrorCol[q])) {
        st.maxMirror[q] = m;
        st.maxMirrorCol[q] = c;
      }
      if (scanFlags[c] & (1 << (1 - q))) {
        st.notScanned[q]++;
        st.notScannedCol[q] = c;
      }
      if (scanFlags[c] & (4 << (1 - q))) st.skipped[q]++;
    }
    st.stamp = numMatrixLinks;
    return st;
  };
  // a row blocked by a column that has since been deleted (fixed): its
  // statistics are recomputed once, a deleted column is in no relation
  auto mirrorBlockerDeleted = [&](HighsInt row, HighsInt q) {
    const MirrorRowStats& st = mirrorRows[row];
    return (st.maxMirror[q] >= rowsize[row] && st.maxMirrorCol[q] != -1 &&
            colDeleted[st.maxMirrorCol[q]]) ||
           (st.notScanned[q] > 0 && colDeleted[st.notScannedCol[q]]);
  };

  // research (presolve_domcol_pair_once): each relation s x_a ≻ t x_b is
  // listed by a (its row of sign s) and, as -t x_b ≻ -s x_a, by b (its row of
  // sign -t). It is tested once, by the side with the smaller static key
  // (length of that listing row at the start of the pass, column index).
  // Each row keeps its entries sorted by their key, so a column reads only
  // the entries it owns. When predictive analysis switches off, the pairs
  // already handed to columns not yet visited are tested at once (forced
  // scan); after the switch a pair is tested by the first column whose list
  // runs. A list that did not run in full is flagged and its pairs are then
  // tested by the other side.
  const bool pairOnce = options->presolve_domcol_pair_once && !fvs;
  struct SignTrackingGuard {
    HPresolve& presolve;
    ~SignTrackingGuard() {
      presolve.domcolSignTracking = false;
      presolve.domcolFvsTracking = false;
    }
  } signTrackingGuard{*this};

  // research (presolve_domcol_first_visit): a pair is tested when the first
  // of its two columns is visited, as scan-both does, but it is listed only
  // from the shorter of its two rows (static key = length of the column's
  // shortest row of that sign at the start of the call, column index). The
  // visited column reads the entries of its own key row whose mirror list is
  // not shorter (fvsOwnF: no mirror list, fvsOwnHT: longer or equal), and,
  // in its shorter rows of the other sign, the columns that use that row as
  // their key row (scanners). Columns whose vector changed (touched) are
  // offered through the extra lists; relations found are kept for the later
  // column (pending). See FABLE_DESIGN.md.
  const bool fvsVerify = fvs && options->presolve_domcol_fvs_verify;
  std::vector<HighsInt> fvsKeyLen;
  std::vector<HighsInt> fvsKeyRow;
  std::vector<HighsInt> fvsLen0;
  // scanners of (row, sign): CSR over 2 * row + sign, columns ascending
  std::vector<HighsInt> fvsScanStart;
  std::vector<HighsInt> fvsScanCol;
  std::vector<std::vector<HighsInt>> fvsOwnF;
  std::vector<std::vector<HighsInt>> fvsOwnHT;
  std::vector<size_t> fvsOwnStamp;
  // candidates of the current scan (stamp = scan id); count only = 1
  std::vector<size_t> fvsCandStamp;
  std::vector<uint8_t> fvsCandCountOnly;
  std::vector<HighsInt> fvsList;
  size_t fvsScanId = 0;
  // pending entries per later column: earlier column, flag bit 0 = sign of
  // the later column's scan, bit 1 = count only
  std::vector<HighsInt> fvsPendHead;
  std::vector<HighsInt> fvsPendNext;
  std::vector<HighsInt> fvsPendCol;
  std::vector<uint8_t> fvsPendFlag;
  // treatment of the entry being processed: 0 = as scan-both, 1 = count
  // only, 2 = verify only
  HighsInt fvsTreat = 0;
  size_t numFvsOffered = 0;
  size_t numFvsPredScans = 0;
  size_t numFvsFixScans = 0;
  size_t numFvsFullScans = 0;
  size_t numFvsFallbacks = 0;
  size_t numFvsPendingUsed = 0;
  size_t numFvsMissed = 0;
  // closed-form count: smallest and largest |coefficient| per row (stamp =
  // links + in-place changes; removals only narrow the range), entry
  // positions of the candidates, scan counts
  std::vector<double> fvsAbsMin;
  std::vector<double> fvsAbsMax;
  std::vector<size_t> fvsAbsStamp;
  std::vector<HighsInt> fvsPos;
  size_t numFvsClosedScans = 0;
  size_t numFvsWalkScans = 0;
  size_t numFvsClosedWalks = 0;
  size_t numFvsRowScans = 0;
  // the type counts of a row cover integer, implied integer and continuous
  // columns only
  bool fvsSemi = false;
  if (fvs)
    for (HighsInt c = 0; c < model->num_col_ && !fvsSemi; ++c)
      fvsSemi = model->integrality_[c] == HighsVarType::kSemiContinuous ||
                model->integrality_[c] == HighsVarType::kSemiInteger;
  auto fvsCoefRange = [&](HighsInt row) {
    const size_t stamp = numMatrixLinks + domcolFvsCoefEpoch;
    if (fvsAbsStamp[row] == stamp) return;
    double lo = kHighsInf;
    double hi = 0.0;
    for (const HighsSliceNonzero& nonz : getRowVector(row)) {
      lo = std::min(lo, std::abs(nonz.value()));
      hi = std::max(hi, std::abs(nonz.value()));
    }
    fvsAbsMin[row] = lo;
    fvsAbsMax[row] = hi;
    fvsAbsStamp[row] = stamp;
  };
  if (fvs) {
    fvsAbsMin.assign(model->num_row_, 0.0);
    fvsAbsMax.assign(model->num_row_, 0.0);
    fvsAbsStamp.assign(model->num_row_, ~size_t{0});
    domcolFvsCountRow = -1;
    domcolFvsCountRemoved.clear();
    const size_t numCol2 = 2 * static_cast<size_t>(model->num_col_);
    domcolSignCount.assign(numCol2, 0);
    fvsKeyLen.assign(numCol2, kHighsIInf);
    fvsKeyRow.assign(numCol2, -1);
    fvsLen0.assign(rowsize.begin(), rowsize.begin() + model->num_row_);
    fvsScanStart.assign(2 * static_cast<size_t>(model->num_row_) + 1, 0);
    for (HighsInt c = 0; c < model->num_col_; ++c) {
      if (colDeleted[c]) continue;
      for (const HighsSliceNonzero& nonz : getColumnVector(c)) {
        HighsInt q = entrySign(nonz.index(), nonz.value());
        domcolSignCount[2 * c + q]++;
        if (rowsize[nonz.index()] < fvsKeyLen[2 * c + q]) {
          fvsKeyLen[2 * c + q] = rowsize[nonz.index()];
          fvsKeyRow[2 * c + q] = nonz.index();
        }
      }
      for (HighsInt q = 0; q < 2; ++q)
        if (fvsKeyRow[2 * c + q] != -1)
          fvsScanStart[2 * fvsKeyRow[2 * c + q] + q + 1]++;
    }
    for (size_t i = 1; i < fvsScanStart.size(); ++i)
      fvsScanStart[i] += fvsScanStart[i - 1];
    fvsScanCol.resize(fvsScanStart.back());
    std::vector<HighsInt> fill(fvsScanStart.begin(), fvsScanStart.end() - 1);
    for (HighsInt c = 0; c < model->num_col_; ++c)
      for (HighsInt q = 0; q < 2; ++q)
        if (fvsKeyRow[2 * c + q] != -1)
          fvsScanCol[fill[2 * fvsKeyRow[2 * c + q] + q]++] = c;
    fvsOwnF.resize(model->num_row_);
    fvsOwnHT.resize(model->num_row_);
    fvsOwnStamp.assign(model->num_row_, ~size_t{0});
    fvsCandStamp.assign(model->num_col_, 0);
    fvsCandCountOnly.assign(model->num_col_, 0);
    fvsPendHead.assign(model->num_col_, -1);
    domcolFvsTouched.assign(model->num_col_, -1);
    domcolFvsExtra.clear();
    domcolFvsExtra.resize(model->num_row_);
    domcolFvsTouchEpoch = 0;
    domcolFvsNumTouched = 0;
    domcolFvsNumExtra = 0;
    domcolFvsVisitCol = -1;
    domcolSignsDirty = false;
    domcolSignTracking = true;
    domcolFvsTracking = true;
  }
  // owned entries of a row, by column; rebuilt after a matrix insertion
  auto fvsOwned = [&](HighsInt row) {
    if (fvsOwnStamp[row] == numMatrixLinks) return;
    fvsOwnF[row].clear();
    fvsOwnHT[row].clear();
    getRowPositions(row, mirror_rowpositions);
    for (HighsInt pos : mirror_rowpositions) {
      if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
      HighsInt c = Acol[pos];
      if (colDeleted[c]) continue;
      HighsInt m = fvsKeyLen[2 * c + 1 - entrySign(row, Avalue[pos])];
      if (m == kHighsIInf)
        fvsOwnF[row].push_back(c);
      else if (m >= fvsLen0[row])
        fvsOwnHT[row].push_back(c);
    }
    fvsOwnStamp[row] = numMatrixLinks;
  };
  // last column visited while predictive analysis was on, once it is off
  HighsInt onceSwitchCol = -1;
  // lists that left owned pairs untested, and their columns (partners
  // look them up in every list)
  size_t numOnceLost = 0;
  std::vector<HighsInt> onceLostCols;
  std::vector<std::vector<std::pair<HighsInt, HighsInt>>> onceSorted;
  std::vector<size_t> onceSortedStamp;
  std::vector<HighsInt> oncePrefix;
  // partners offered in the current list (stamp = list id)
  std::vector<size_t> onceOffered;
  size_t onceListId = 0;
  size_t numOnceMoved = 0;
  // pairs tested before the switch: owned / partner's list open
  size_t numOnceWhy[2] = {0, 0};
  HighsInt onceLostCol = -1;
  size_t numPrefixLists = 0;
  size_t numIncompleteLists = 0;
  size_t numForcedLists = 0;
  if (pairOnce) {
    domcolSignCount.assign(2 * static_cast<size_t>(model->num_col_), 0);
    mirrorLen.assign(2 * static_cast<size_t>(model->num_col_), kHighsIInf);
    for (HighsInt c = 0; c < model->num_col_; ++c) {
      if (colDeleted[c]) continue;
      for (const HighsSliceNonzero& nonz : getColumnVector(c)) {
        HighsInt q = entrySign(nonz.index(), nonz.value());
        domcolSignCount[2 * c + q]++;
        mirrorLen[2 * c + q] =
            std::min(mirrorLen[2 * c + q], rowsize[nonz.index()]);
      }
    }
    domcolSignsDirty = false;
    domcolSignTracking = true;
    scanFlags.assign(model->num_col_, 0);
    onceOffered.assign(model->num_col_, 0);
    onceSorted.resize(model->num_row_);
    onceSortedStamp.assign(model->num_row_, ~size_t{0});
  }
  // (key, column) of a: lexicographic order
  auto onceBefore = [&](HighsInt lenA, HighsInt a, HighsInt lenB, HighsInt b) {
    return lenA < lenB || (lenA == lenB && a < b);
  };
  // entries of the row with the key of the partner side, largest first
  auto sortedRow =
      [&](HighsInt row) -> const std::vector<std::pair<HighsInt, HighsInt>>& {
    std::vector<std::pair<HighsInt, HighsInt>>& v = onceSorted[row];
    if (onceSortedStamp[row] == numMatrixLinks) return v;
    v.clear();
    getRowPositions(row, mirror_rowpositions);
    for (HighsInt pos : mirror_rowpositions) {
      if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
      HighsInt c = Acol[pos];
      if (colDeleted[c]) continue;
      v.emplace_back(mirrorLen[2 * c + 1 - entrySign(row, Avalue[pos])], c);
    }
    std::sort(v.begin(), v.end(),
              [](const std::pair<HighsInt, HighsInt>& x,
                 const std::pair<HighsInt, HighsInt>& y) { return x > y; });
    onceSortedStamp[row] = numMatrixLinks;
    return v;
  };

  // research (measurement only, dev log): domination tests and relations
  // found per kind (direction, direction_k), distinct relations (y ≻ z and
  // -z ≻ -y counted once)
  size_t testsKind[4] = {0, 0, 0, 0};
  size_t foundKind[4] = {0, 0, 0, 0};
  const bool countDistinct =
      options->log_dev_level >= kHighsLogDevLevelVerbose;
  std::unordered_set<uint64_t> distinctFound;

  for (HighsInt j = 0; j < model->num_col_; ++j) {
    // skip deleted columns
    if (colDeleted[j]) continue;

    // research (presolve_domcol_first_visit)
    if (fvs) domcolFvsVisitCol = j;

    // increment counter for number of columns
    numCols++;

    // initialise
    HighsInt bestRowPlus = -1;
    HighsInt bestRowPlusLen = kHighsIInf;
    double ajBestRowPlus = 0.0;
    HighsInt bestRowMinus = -1;
    HighsInt bestRowMinusLen = kHighsIInf;
    double ajBestRowMinus = 0.0;

    for (const HighsSliceNonzero& nonz : getColumnVector(j)) {
      HighsInt row = nonz.index();
      HighsInt scale = model->row_upper_[row] != kHighsInf ? 1 : -1;

      double val = scale * nonz.value();
      if (val > 0.0 && rowsize[row] < bestRowPlusLen) {
        bestRowPlus = row;
        bestRowPlusLen = rowsize[row];
        ajBestRowPlus = nonz.value();
      }

      if (val < 0.0 && rowsize[row] < bestRowMinusLen) {
        bestRowMinus = row;
        bestRowMinusLen = rowsize[row];
        ajBestRowMinus = nonz.value();
      }
    }

    // lambda for fixing variables
    auto fixCol = [&](HighsInt col, HighsInt direction) {
      numFixedCols++;
      if (direction > 0) {
        HPRESOLVE_CHECKED_CALL(fixColToUpper(postsolve_stack, col));
      } else {
        HPRESOLVE_CHECKED_CALL(fixColToLower(postsolve_stack, col));
      }
      // remove row singletons and doubleton equations
      HPRESOLVE_CHECKED_CALL(removeRowSingletons(postsolve_stack));
      HPRESOLVE_CHECKED_CALL(removeDoubletonEquations(postsolve_stack));
      return Result::kOk;
    };

    // Predictive bound analysis (Theorem 3 from Gamrath et al. 2015).
    // The paper defines x_j ≻ x_k (j dominates k). The code checks
    // (direction * x_col) ≻ (direction_k * x_otherCol):
    //   direction = +1, multiplier = +1: x_j =  x_col,      x_k =  x_otherCol
    //   direction = +1, multiplier = -1: x_j =  x_col,      x_k = -x_otherCol
    //   direction = -1, multiplier = +1: x_j =  x_otherCol, x_k =  x_col
    //   direction = -1, multiplier = -1: x_j = -x_col,      x_k =  x_otherCol
    // col is the column being tightened, otherCol is the conditioning
    // column (whose value otherColBound is substituted).
    // colIsAtUpper = true : col = x_j, apply (i)/(iii)/(v)
    // colIsAtUpper = false: col = x_k, apply (ii)/(iv)/(vi)
    // otherColCoeffPattern: +1 = same-sign, -1 = opposite-sign coefficient
    //                       filter (opposite signs from negated-column
    //                       domination)
    auto tightenBounds = [&](HighsInt col, double colBound, bool colIsAtUpper,
                             HighsInt otherCol, double otherColBound,
                             HighsInt otherColCoeffPattern) {
      // bound should be finite
      assert(std::abs(otherColBound) != kHighsInf);
      // return if variable is already fixed
      if (model->col_lower_[col] == model->col_upper_[col]) return Result::kOk;
      // initialise bounds
      double lowerBound = -kHighsInf;
      double upperBound = kHighsInf;
      if (colIsAtUpper) {
        // For negated-column domination the paper's x_k is negated,
        // so (i)/(iii)/(v) below correspond to (ii)/(iv)/(vi) in the
        // paper with negated bounds and cost.
        // (i) x_j <= MINL^k_j(otherColBound)
        upperBound = computeImpliedUpperBound(col, otherCol, otherColBound,
                                              otherColCoeffPattern);
        // (iii) x_j >= min{colBound, MAXL^k_j(otherColBound)}
        lowerBound = std::min(
            colBound, computeImpliedLowerBound(col, otherCol, otherColBound,
                                               otherColCoeffPattern));
        if (model->col_cost_[col] <= 0) {
          // (v) if c_j <= 0, then x_j >= min{colBound,
          //                                  MINU^k_j(otherColBound)}
          double worstCaseUpper = computeWorstCaseUpperBound(
              col, otherCol, otherColBound, otherColCoeffPattern);
          lowerBound = std::max(lowerBound, std::min(colBound, worstCaseUpper));
        }
      } else {
        // For negated-column domination the paper's x_j is negated,
        // so (ii)/(iv)/(vi) below correspond to (i)/(iii)/(v) in the
        // paper with negated bounds and cost.
        // (ii) x_k >= MAXL^j_k(otherColBound)
        lowerBound = computeImpliedLowerBound(col, otherCol, otherColBound,
                                              otherColCoeffPattern);
        // (iv) x_k <= max{colBound, MINL^j_k(otherColBound)}
        upperBound = std::max(
            colBound, computeImpliedUpperBound(col, otherCol, otherColBound,
                                               otherColCoeffPattern));
        if (model->col_cost_[col] >= 0) {
          // (vi) if c_k >= 0, then x_k <= max{colBound,
          //                                   MAXU^j_k(otherColBound)}
          double worstCaseLower = computeWorstCaseLowerBound(
              col, otherCol, otherColBound, otherColCoeffPattern);
          upperBound = std::min(upperBound, std::max(colBound, worstCaseLower));
        }
      }
      // update bounds
      if (lowerBound < kHighsInf &&
          lowerBound > model->col_lower_[col] + primal_feastol) {
        if (lowerBound == model->col_upper_[col]) {
          numFixedColsPredBndAnalysis++;
          return fixCol(col, HighsInt{1});
        } else if (model->integrality_[col] != HighsVarType::kContinuous) {
          numModifiedBndsPredBndAnalysis++;
          HPRESOLVE_CHECKED_CALL(changeColLower(col, lowerBound));
        }
      }
      if (upperBound > -kHighsInf &&
          upperBound < model->col_upper_[col] - primal_feastol) {
        if (upperBound == model->col_lower_[col]) {
          numFixedColsPredBndAnalysis++;
          return fixCol(col, HighsInt{-1});
        } else if (model->integrality_[col] != HighsVarType::kContinuous) {
          numModifiedBndsPredBndAnalysis++;
          HPRESOLVE_CHECKED_CALL(changeColUpper(col, upperBound));
        }
      }
      return Result::kOk;
    };

    // lambda for checking whether two variables have the same type
    auto varsHaveSameType = [&](HighsInt col1, HighsInt col2) {
      return ((model->integrality_[col1] != HighsVarType::kContinuous &&
               model->integrality_[col2] != HighsVarType::kContinuous) ||
              (model->integrality_[col1] != HighsVarType::kInteger &&
               model->integrality_[col2] != HighsVarType::kInteger));
    };

    // lambda for (1) checking whether one of the two columns is dominated by
    // the other one and (2) fixing variables or strengthening bounds
    auto checkCols = [&](HighsInt row, HighsInt col, HighsInt k,
                         HighsInt direction, HighsInt multiplier,
                         bool boundImplied, bool hasCliques, bool sameVarType,
                         bool twoWay, bool relied, bool kImplied,
                         bool kCliques) {
      // compute direction for dominated variable
      // (1: lower bound; -1: upper bound)
      HighsInt direction_k = multiplier * direction;
      // get bounds
      double dominatingBound =
          direction > 0 ? model->col_upper_[col] : model->col_lower_[col];
      double dominatedBound =
          direction_k > 0 ? model->col_lower_[k] : model->col_upper_[k];
      // check if bounds are finite
      bool isDominatingBoundFinite = direction * dominatingBound != kHighsInf;
      bool isDominatedBoundFinite = direction_k * dominatedBound != -kHighsInf;
      // check whether variable 'k' can potentially be fixed. check if there are
      // cliques in advance instead of directly searching for a common clique.
      bool tryToFix = isDominatedBoundFinite && (boundImplied || hasCliques);
      // check whether predictive bound analysis can be performed. both
      // variables need to have the same type.
      bool tryToStrengthenBounds =
          (isDominatingBoundFinite || isDominatedBoundFinite) && sameVarType;
      // research (presolve_domcol_mirror_skip): the mirror -z ≻ -y fixes col
      // at its dominating bound when k's opposite bound is implied or a
      // clique links the two complementary literals
      bool tryToFixCol =
          twoWay && isDominatingBoundFinite && (kImplied || kCliques);
      if (tryToFix || tryToFixCol || tryToStrengthenBounds) {
        // research (presolve_domcol_first_visit): pair not offered: count
        // it as scan-both does (1), or only test it for the verify option
        if (fvsTreat != 0) {
          if (fvsTreat == 1 && !tryToFix) numDomChecksPredBndAnalysis++;
          if (fvsVerify) {
            const size_t checks = numDomChecks;
            if (checkDomination(direction, col, direction_k, k))
              numFvsMissed++;
            if (fvsTreat == 2) numDomChecks = checks;
          } else if (fvsTreat == 1) {
            numDomChecks++;
          }
          return Result::kOk;
        }
        // increment counter for number of domination checks due to predictive
        // bound analysis
        // (pair once: counted when this column's own fixing is not possible,
        // as in the original rule)
        if (!tryToFix && (pairOnce || !tryToFixCol))
          numDomChecksPredBndAnalysis++;
        // check for domination
        const HighsInt kind = (direction > 0 ? 2 : 0) + (direction_k > 0 ? 1 : 0);
        testsKind[kind]++;
        bool dominated = checkDomination(direction, col, direction_k, k);
        if (dominated) {
          foundKind[kind]++;
          if (countDistinct) {
            // canonical form: the lower column index first
            HighsInt lo = col, hi = k, slo = direction, shi = direction_k;
            if (k < col) {
              lo = k;
              hi = col;
              slo = -direction_k;
              shi = -direction;
            }
            distinctFound.insert((static_cast<uint64_t>(lo) << 33) |
                                 (static_cast<uint64_t>(hi) << 2) |
                                 (slo > 0 ? 2u : 0u) | (shi > 0 ? 1u : 0u));
          }
        }
        auto canFixCol = [&]() {
          return tryToFixCol &&
                 (kImplied ||
                  mipsolver->mipdata_->cliquetable.haveCommonClique(
                      HighsCliqueTable::CliqueVar(k, direction_k > 0 ? 0 : 1),
                      HighsCliqueTable::CliqueVar(col, direction > 0 ? 0 : 1)));
        };
        // a relied pair was found first from k's side in a full scan, so try
        // its fixing first
        if (dominated && relied && canFixCol()) {
          numMirrorFixCol++;
          HPRESOLVE_CHECKED_CALL(fixCol(col, direction));
        } else if (dominated) {
          if (tryToFix &&
              (boundImplied ||
               mipsolver->mipdata_->cliquetable.haveCommonClique(
                   HighsCliqueTable::CliqueVar(col, direction > 0 ? 1 : 0),
                   HighsCliqueTable::CliqueVar(k, direction_k > 0 ? 1 : 0)))) {
            // direction =  1, multiplier =  1:
            // case (i)   ub(x_j) =  inf,  x_j >  x_k: set x_k = lb(x_k)
            // direction =  1, multiplier = -1:
            // case (ii)  ub(x_j) =  inf,  x_j > -x_k: set x_k = ub(x_k)
            // direction = -1, multiplier =  1:
            // case (iii) lb(x_j) = -inf, -x_j > -x_k: set x_k = ub(x_k)
            // direction = -1, multiplier = -1:
            // case (iv)  lb(x_j) = -inf, -x_j >  x_k: set x_k = lb(x_k)
            HPRESOLVE_CHECKED_CALL(fixCol(k, -direction_k));
          } else if (!relied && canFixCol()) {
            numMirrorFixCol++;
            HPRESOLVE_CHECKED_CALL(fixCol(col, direction));
          } else if (tryToStrengthenBounds) {
            // tighten bounds via predictive bound analysis, see Theorem 3
            // from Gamrath et al.'s paper
            if (isDominatedBoundFinite)
              HPRESOLVE_CHECKED_CALL(
                  tightenBounds(col, dominatingBound, direction > 0, k,
                                dominatedBound, direction * direction_k));
            if (!colDeleted[col] && isDominatingBoundFinite)
              HPRESOLVE_CHECKED_CALL(
                  tightenBounds(k, dominatedBound, direction_k < 0, col,
                                dominatingBound, direction * direction_k));
          }
        }
        // research (presolve_domcol_first_visit): a relation found is kept
        // for the later column's scan of sign -direction_k; when only
        // possible dominations count, a signature-possible pair that failed
        // is kept too, to be counted there (no test)
        if (fvs && k > col && !colDeleted[col] && !colDeleted[k] &&
            (dominated ||
             (domcolCountPossible &&
              checkSignatures(direction, col, direction_k, k)))) {
          fvsPendCol.push_back(col);
          fvsPendFlag.push_back(static_cast<uint8_t>(
              (direction_k > 0 ? 0 : 1) | (dominated ? 0 : 2)));
          fvsPendNext.push_back(fvsPendHead[k]);
          fvsPendHead[k] = static_cast<HighsInt>(fvsPendCol.size()) - 1;
        }
      }
      return Result::kOk;
    };

    // row positions, from the row cache when it is on
    auto positionsOf = [&](HighsInt row) -> const std::vector<HighsInt>& {
      if (!rowCache) {
        getRowPositions(row, check_rowpositions);
        return check_rowpositions;
      }
      if (cache_rowstamp[row] != numMatrixLinks) {
        getRowPositions(row, cache_rowpositions[row]);
        cache_rowstamp[row] = numMatrixLinks;
      }
      return cache_rowpositions[row];
    };

    // research (presolve_domcol_pair_once): test direction * x_col ≻
    // dirK * x_k once, with both fixings; row is the listing row, aj and ak
    // the two coefficients in it
    auto checkPairOnce = [&](HighsInt row, HighsInt col, HighsInt k,
                             HighsInt direction, HighsInt dirK, double aj,
                             double ak, bool hasCliques, bool forced) {
      if (k == col || colDeleted[k]) return Result::kOk;
      // the kind must fit the signs in this row (else it is no pair)
      if (!checkDominationNonZero(row, direction * aj, dirK * ak))
        return Result::kOk;
      // col lists the pair in its row of sign qc, k in its row of sign qk
      const HighsInt qc = direction > 0 ? 1 : 0;
      const HighsInt qk = dirK > 0 ? 0 : 1;
      const bool colOwns =
          onceBefore(mirrorLen[2 * col + qc], col, mirrorLen[2 * k + qk], k);
      // k visited and its list did not run in full
      const bool kOpen = k < col && (scanFlags[k] & (1 << qk)) != 0;
      bool test;
      if (forced)
        // switch: pairs col handed to a column not yet visited
        test = !colOwns && k > onceSwitchCol;
      else if (onceSwitchCol < 0 || col <= onceSwitchCol)
        test = colOwns || kOpen;
      else if (k > col)
        test = true;
      else if (k <= onceSwitchCol)
        // k handed the pair to col: tested by k's forced scan if it ran
        test = colOwns ? (scanFlags[k] & (4 << qk)) == 0 : kOpen;
      else
        test = kOpen;
      if (!test) return Result::kOk;
      if (!forced && (onceSwitchCol < 0 || col <= onceSwitchCol))
        numOnceWhy[colOwns ? 0 : 1]++;
      numPairs++;
      if (domcolCountPossible &&
          !checkSignatures(direction, col, direction, k) &&
          !checkSignatures(direction, col, -direction, k))
        return Result::kOk;
      if (options->presolve_domcol_signature_first &&
          !checkSignatures(direction, col, direction, k) &&
          !checkSignatures(direction, col, -direction, k) &&
          (!allowPredBndAnalysis ||
           ((hasCliques ||
             (direction > 0 ? isUpperImplied(col) : isLowerImplied(col))) &&
            model->col_lower_[k] != -kHighsInf &&
            model->col_upper_[k] != kHighsInf)))
        return Result::kOk;
      numPairsChecked++;
      bool sameVarType = varsHaveSameType(col, k);
      bool boundImplied =
          direction > 0 ? isUpperImplied(col) : isLowerImplied(col);
      bool kImplied = dirK > 0 ? isLowerImplied(k) : isUpperImplied(k);
      bool kCliques = isBinary(k) && mipsolver->mipdata_->cliquetable.numCliques(
                                         k, dirK > 0 ? 0 : 1) > 0;
      if (!boundImplied && !hasCliques && !sameVarType && !kImplied &&
          !kCliques)
        return Result::kOk;
      return checkCols(row, col, k, direction, direction * dirK, boundImplied,
                       hasCliques, sameVarType, true, false, kImplied,
                       kCliques);
    };

    // research (presolve_domcol_pair_once): offer the entry at pos to
    // direction * x_col, both kinds; false when col or row is gone
    auto offerEntry = [&](HighsInt row, HighsInt col, HighsInt pos,
                          HighsInt direction, double aj, bool hasCliques,
                          bool forced, bool& alive) {
      alive = true;
      HighsInt k = Acol[pos];
      // offered once per list, also when the list moves to another row
      if (onceOffered[k] == onceListId) return Result::kOk;
      onceOffered[k] = onceListId;
      HPRESOLVE_CHECKED_CALL(checkPairOnce(row, col, k, direction, direction,
                                           aj, Avalue[pos], hasCliques,
                                           forced));
      alive = !colDeleted[col] && !rowDeleted[row];
      if (!alive || colDeleted[k] || Avalue[pos] == 0.0 || Arow[pos] != row)
        return Result::kOk;
      HPRESOLVE_CHECKED_CALL(checkPairOnce(row, col, k, direction, -direction,
                                           aj, Avalue[pos], hasCliques,
                                           forced));
      alive = !colDeleted[col] && !rowDeleted[row];
      return Result::kOk;
    };

    // research (presolve_domcol_pair_once): list the partners of direction
    // * x_col from a row of that sign; before the switch only the entries
    // with a larger key are read (sorted list), unless the keys may be stale
    // or a list left owned pairs open; complete = every partner was offered
    auto listInRow = [&](HighsInt row, HighsInt col, HighsInt direction,
                         double aj, bool hasCliques, bool forced,
                         bool& complete) {
      complete = false;
      if (rowDeleted[row]) return Result::kOk;
      bool alive = true;
      if (!forced && onceSwitchCol < 0 && !domcolSignsDirty) {
        const std::vector<std::pair<HighsInt, HighsInt>>& v = sortedRow(row);
        const HighsInt len = mirrorLen[2 * col + (direction > 0 ? 1 : 0)];
        size_t p = 0;
        while (p < v.size() && onceBefore(len, col, v[p].first, v[p].second))
          ++p;
        // columns whose list left owned pairs open are looked up directly,
        // unless that costs more than reading the rest of the row
        if (p < v.size() && onceLostCols.size() < v.size() - p) {
          numPrefixLists++;
          oncePrefix.clear();
          for (size_t i = 0; i < p; ++i) oncePrefix.push_back(v[i].second);
          for (HighsInt c : onceLostCols) oncePrefix.push_back(c);
          // row order (by column index), as a full scan
          std::sort(oncePrefix.begin(), oncePrefix.end());
          for (HighsInt k : oncePrefix) {
            if (colDeleted[k]) continue;
            HighsInt pos = findNonzero(row, k);
            if (pos == -1) continue;
            HPRESOLVE_CHECKED_CALL(offerEntry(row, col, pos, direction, aj,
                                              hasCliques, false, alive));
            if (!alive) return Result::kOk;
          }
          complete = true;
          return Result::kOk;
        }
      }
      const std::vector<HighsInt>& rowpositions = positionsOf(row);
      for (HighsInt pos : rowpositions) {
        if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
        HPRESOLVE_CHECKED_CALL(offerEntry(row, col, pos, direction, aj,
                                          hasCliques, forced, alive));
        if (!alive) return Result::kOk;
      }
      complete = true;
      return Result::kOk;
    };

    // a row deleted during the scan (e.g. a covering row satisfied by a
    // fixing): every other row of the same sign is a complete list too, so
    // the list goes on in the shortest one
    auto listFromRow = [&](HighsInt row, HighsInt col, HighsInt direction,
                           double aj, bool hasCliques, bool forced,
                           bool& complete) {
      ++onceListId;
      const HighsInt q = direction > 0 ? 1 : 0;
      while (true) {
        HPRESOLVE_CHECKED_CALL(listInRow(row, col, direction, aj, hasCliques,
                                         forced, complete));
        if (complete || colDeleted[col]) return Result::kOk;
        row = -1;
        HighsInt rowLen = kHighsIInf;
        for (const HighsSliceNonzero& nonz : getColumnVector(col)) {
          if (entrySign(nonz.index(), nonz.value()) != q ||
              rowsize[nonz.index()] >= rowLen)
            continue;
          row = nonz.index();
          rowLen = rowsize[row];
          aj = nonz.value();
        }
        if (row == -1) return Result::kOk;
        numOnceMoved++;
      }
    };

    // lambda for one entry of the row scanned by checkRow; stop = the column
    // or the row is gone
    auto checkEntry = [&](HighsInt row, HighsInt col, HighsInt pos,
                          HighsInt direction, double bestVal, bool hasCliques,
                          bool reliedOnly, bool& stop) {
      stop = false;
      do {
        // get column index
        HighsInt k = Acol[pos];

        // skip column 'col' and deleted columns
        if (k == col || colDeleted[k]) continue;

        // research (presolve_domcol_mirror_skip): k relied on this scan when
        // it skipped its row of sign -direction; the pair then also tries
        // k's fixing (same-sign pairs only, see DERIVATION.md section 6)
        bool relied = false;
        if (mirrorSkip)
          relied = (scanFlags[k] & (4 << (direction > 0 ? 0 : 1))) != 0;
        const bool twoWay = relied;
        if (reliedOnly && !relied) continue;
        numPairs++;

        // research (presolve_domcol_count_possible): skip pairs whose
        // signatures rule out domination in both directions, so they do not
        // count as predictive bound analysis work
        if (domcolCountPossible &&
            !checkSignatures(direction, col, direction, k) &&
            !checkSignatures(direction, col, -direction, k))
          continue;

        // research (presolve_domcol_signature_first): same skip, but only
        // when the pair would not count as predictive bound analysis work
        // anyway (analysis off, or a fixing possible), so the result is
        // unchanged
        if (options->presolve_domcol_signature_first &&
            !checkSignatures(direction, col, direction, k) &&
            !checkSignatures(direction, col, -direction, k) &&
            (!allowPredBndAnalysis ||
             ((hasCliques ||
               (direction > 0 ? isUpperImplied(col) : isLowerImplied(col))) &&
              model->col_lower_[k] != -kHighsInf &&
              model->col_upper_[k] != kHighsInf)))
          continue;
        numPairsChecked++;

        // get coefficient
        double ak = Avalue[pos];

        // check if variables have the same type
        bool sameVarType = varsHaveSameType(col, k);

        // check if bound is implied (computed fresh due to earlier fixings)
        bool boundImplied =
            direction > 0 ? isUpperImplied(col) : isLowerImplied(col);

        // k's side of the mirror: its bound opposite to direction implied,
        // or cliques on that literal
        bool kImplied = false;
        bool kCliques = false;
        if (twoWay) {
          kImplied = direction > 0 ? isLowerImplied(k) : isUpperImplied(k);
          kCliques = isBinary(k) &&
                     mipsolver->mipdata_->cliquetable.numCliques(
                         k, direction > 0 ? 0 : 1) > 0;
        }

        // skip checks if nothing to do
        if (!boundImplied && !hasCliques && !sameVarType && !kImplied &&
            !kCliques)
          continue;

        // try to fix variables or strengthen bounds
        // check already known non-zeros in respective columns in advance to
        // avoid (potentially slow) element-wise comparison if possible.
        if (checkDominationNonZero(row, direction * bestVal, direction * ak)) {
          HPRESOLVE_CHECKED_CALL(checkCols(row, col, k, direction, HighsInt{1},
                                           boundImplied, hasCliques,
                                           sameVarType, twoWay, relied,
                                           kImplied, kCliques));
          if (colDeleted[col] || rowDeleted[row]) break;
        }

        if (!reliedOnly && !colDeleted[k] && Avalue[pos] != 0.0 &&
            Arow[pos] == row &&
            checkDominationNonZero(row, direction * bestVal, -direction * ak)) {
          HPRESOLVE_CHECKED_CALL(checkCols(row, col, k, direction, HighsInt{-1},
                                           boundImplied, hasCliques,
                                           sameVarType, false, false, false,
                                           false));
          if (colDeleted[col] || rowDeleted[row]) break;
        }
      } while (false);
      // only checkCols changes the model, and the scan stops right after it
      stop = colDeleted[col] || rowDeleted[row];
      return Result::kOk;
    };

    // lambda for finding a domination relationship in the given row
    auto checkRow = [&](HighsInt row, HighsInt col, HighsInt direction,
                        double bestVal, bool hasCliques, bool reliedOnly) {
      if (rowDeleted[row]) return Result::kOk;
      std::vector<HighsInt>* rowpositions = &check_rowpositions;
      if (rowCache) {
        rowpositions = &cache_rowpositions[row];
        if (cache_rowstamp[row] != numMatrixLinks) {
          getRowPositions(row, *rowpositions);
          cache_rowstamp[row] = numMatrixLinks;
        }
      } else {
        getRowPositions(row, check_rowpositions);
      }
      bool stop = false;
      for (HighsInt pos : *rowpositions) {
        if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
        HPRESOLVE_CHECKED_CALL(checkEntry(row, col, pos, direction, bestVal,
                                          hasCliques, reliedOnly, stop));
        if (stop) break;
      }
      return Result::kOk;
    };

    // research (presolve_domcol_first_visit): scan of direction * x_col in
    // its current shortest row of that sign. Fix scans, touched columns and
    // stale signs: scan-both's scan. Otherwise the candidates are collected
    // from the static lists and each gets scan-both's processing of its
    // entry in the row; the other entries are only counted (walk of the
    // row), or, when only possible dominations count, not read at all.
    auto fvsScan = [&](HighsInt row, HighsInt col, HighsInt direction,
                       double bestVal, bool hasCliques, bool ownFix) {
      if (rowDeleted[row]) return Result::kOk;
      const HighsInt q = direction > 0 ? 1 : 0;
      const HighsInt keyRow = fvsKeyRow[2 * col + q];
      if (ownFix || domcolSignsDirty || domcolFvsTouched[col] >= 0 ||
          keyRow == -1) {
        if (ownFix)
          numFvsFixScans++;
        else
          numFvsFullScans++;
        return checkRow(row, col, direction, bestVal, hasCliques, false);
      }
      // research (presolve_domcol_first_visit): the lists against the row,
      // before collecting. Each list entry counted here is read once by the
      // collection below (its duplicates too), scan-both reads the
      // rowsize - 1 other entries of the row and tests no more than those.
      // When the lists are not shorter, scan-both's scan is the cheaper of
      // the two and it is run: the tests that hold and the counter are the
      // same (verify: the lists are always used).
      if (!fvsVerify) {
        fvsOwned(keyRow);
        const std::vector<HighsInt>& own = fvsOwnHT[keyRow];
        const size_t limit = static_cast<size_t>(rowsize[row]) - 1;
        size_t listed =
            fvsOwnF[keyRow].size() + domcolFvsExtra[keyRow].size() +
            (own.end() - std::upper_bound(own.begin(), own.end(), col));
        for (const HighsSliceNonzero& nonz : getColumnVector(col)) {
          if (listed >= limit) break;
          HighsInt r = nonz.index();
          if (entrySign(r, nonz.value()) == q ||
              fvsLen0[r] >= fvsKeyLen[2 * col + q])
            continue;
          const HighsInt* first = fvsScanCol.data() + fvsScanStart[2 * r];
          const HighsInt* mid = fvsScanCol.data() + fvsScanStart[2 * r + 1];
          const HighsInt* last = fvsScanCol.data() + fvsScanStart[2 * r + 2];
          listed += (mid - std::upper_bound(first, mid, col)) +
                    (last - std::upper_bound(mid, last, col));
        }
        if (listed >= limit) {
          numFvsRowScans++;
          return checkRow(row, col, direction, bestVal, hasCliques, false);
        }
      }
      numFvsPredScans++;
      ++fvsScanId;
      fvsList.clear();
      auto addCand = [&](HighsInt c, bool countOnly) {
        if (c == col || colDeleted[c]) return;
        if (fvsCandStamp[c] != fvsScanId) {
          fvsCandStamp[c] = fvsScanId;
          fvsCandCountOnly[c] = countOnly ? 1 : 0;
          fvsList.push_back(c);
        } else if (!countOnly) {
          fvsCandCountOnly[c] = 0;
        }
      };
      // own list: entries without a mirror list, and the later columns
      // whose mirror list is not shorter
      fvsOwned(keyRow);
      for (HighsInt c : fvsOwnF[keyRow]) addCand(c, false);
      const std::vector<HighsInt>& ownHT = fvsOwnHT[keyRow];
      for (auto it = std::upper_bound(ownHT.begin(), ownHT.end(), col);
           it != ownHT.end(); ++it)
        addCand(*it, false);
      // shorter rows of the other sign: the later columns listing there
      // FVS TODO: filter a scanner in its own row first (live, sign, kind).
      // Not built: when only possible dominations count, the counter is the
      // tests made, so a filter there changes the switch time; exact only
      // with the walk or the closed-form count below.
      for (const HighsSliceNonzero& nonz : getColumnVector(col)) {
        HighsInt r = nonz.index();
        if (entrySign(r, nonz.value()) == q ||
            fvsLen0[r] >= fvsKeyLen[2 * col + q])
          continue;
        const HighsInt* first = fvsScanCol.data() + fvsScanStart[2 * r];
        const HighsInt* mid = fvsScanCol.data() + fvsScanStart[2 * r + 1];
        const HighsInt* last = fvsScanCol.data() + fvsScanStart[2 * r + 2];
        for (const HighsInt* it = std::upper_bound(first, mid, col); it != mid;
             ++it)
          addCand(*it, false);
        for (const HighsInt* it = std::upper_bound(mid, last, col);
             it != last; ++it)
          addCand(*it, false);
      }
      // touched columns: later ones, and earlier ones changed since their
      // own visit
      for (HighsInt c : domcolFvsExtra[keyRow])
        if (c > col || domcolFvsTouched[c] >= c) addCand(c, false);
      // relations found by earlier columns
      for (HighsInt p = fvsPendHead[col]; p != -1; p = fvsPendNext[p]) {
        if ((fvsPendFlag[p] & 1) != q) continue;
        numFvsPendingUsed++;
        addCand(fvsPendCol[p], (fvsPendFlag[p] & 2) != 0);
      }

      const size_t epoch = domcolFvsTouchEpoch;
      bool stop = false;
      // walk the entries after column 'from' as scan-both does; after a
      // touch (or stale signs) the rest of the row is scan-both's scan
      auto walk = [&](HighsInt from) {
        bool fallback = false;
        const std::vector<HighsInt>& rowpositions = positionsOf(row);
        for (HighsInt pos : rowpositions) {
          if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
          HighsInt k = Acol[pos];
          if (k <= from) continue;
          if (!fallback &&
              (domcolFvsTouchEpoch != epoch || domcolSignsDirty)) {
            fallback = true;
            numFvsFallbacks++;
          }
          if (fallback)
            fvsTreat = 0;
          else if (fvsCandStamp[k] == fvsScanId)
            fvsTreat = fvsCandCountOnly[k];
          else
            fvsTreat = domcolCountPossible ? 2 : 1;
          if (fvsTreat == 0 && k != col && !colDeleted[k]) numFvsOffered++;
          Result result = checkEntry(row, col, pos, direction, bestVal,
                                     hasCliques, false, stop);
          fvsTreat = 0;
          if (result != Result::kOk) return result;
          if (stop) break;
        }
        return Result::kOk;
      };
      // research (presolve_domcol_first_visit): closed-form count. The
      // bound of col is finite and not implied and there are no cliques, so
      // scan-both counts an entry it reaches once per kind that passes the
      // coefficient test, when the types agree. With |a_col| <= every
      // |coefficient| of the row (ranged row: all equal) exactly one kind
      // passes, so the count is the number of live entries of col's type
      // class; the row is not walked.
      bool closed = false;
      if (!domcolCountPossible && !fvsVerify && allowPredBndAnalysis &&
          !hasCliques && !fvsSemi) {
        const double bound =
            direction > 0 ? model->col_upper_[col] : model->col_lower_[col];
        if (direction * bound != kHighsInf &&
            !(direction > 0 ? isUpperImplied(col) : isLowerImplied(col))) {
          fvsCoefRange(row);
          const double absVal = std::abs(bestVal);
          if (isRanged(row))
            closed = fvsAbsMin[row] == absVal && fvsAbsMax[row] == absVal &&
                     2 * absVal > options->small_matrix_value;
          else
            closed = absVal <= fvsAbsMin[row] &&
                     absVal + fvsAbsMin[row] > options->small_matrix_value &&
                     (model->row_upper_[row] == kHighsInf ? -direction
                                                         : direction) *
                             bestVal >
                         0;
        }
      }
      if (closed) {
        numFvsClosedScans++;
        const HighsVarType type = model->integrality_[col];
        size_t count = rowsize[row] - 1;
        if (type == HighsVarType::kContinuous)
          count -= rowsizeInteger[row];
        else if (type == HighsVarType::kInteger)
          count = rowsizeInteger[row] + rowsizeImplInt[row] - 1;
        // the candidates in the row count themselves
        std::sort(fvsList.begin(), fvsList.end());
        fvsPos.clear();
        for (HighsInt k : fvsList) {
          HighsInt pos = findNonzero(row, k);
          if (pos == -1) continue;
          fvsList[fvsPos.size()] = k;
          fvsPos.push_back(pos);
          if (varsHaveSameType(col, k)) --count;
        }
        fvsList.resize(fvsPos.size());
        numDomChecksPredBndAnalysis += count;
        numDomChecks += count;
        // entries after column 'from' that scan-both does not reach, or
        // that are walked instead
        auto uncount = [&](HighsInt from) {
          const std::vector<HighsInt>& rowpositions = positionsOf(row);
          for (HighsInt pos : rowpositions) {
            if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
            HighsInt c = Acol[pos];
            if (c <= from || c == col || colDeleted[c] ||
                fvsCandStamp[c] == fvsScanId || !varsHaveSameType(col, c))
              continue;
            --numDomChecksPredBndAnalysis;
            --numDomChecks;
          }
        };
        domcolFvsCountRow = row;
        domcolFvsCountRemoved.clear();
        HighsInt from = -1;
        bool walkRest = false;
        for (size_t i = 0; i < fvsList.size(); ++i) {
          HighsInt k = fvsList[i];
          HighsInt pos = fvsPos[i];
          if (colDeleted[k] || Avalue[pos] == 0.0 || Arow[pos] != row ||
              Acol[pos] != k)
            continue;
          fvsTreat = fvsCandCountOnly[k];
          if (fvsTreat == 0) numFvsOffered++;
          Result result = checkEntry(row, col, pos, direction, bestVal,
                                     hasCliques, false, stop);
          fvsTreat = 0;
          if (result != Result::kOk) {
            domcolFvsCountRow = -1;
            return result;
          }
          // entries removed before scan-both reaches them
          for (HighsInt c : domcolFvsCountRemoved) {
            if (c <= k || c == col || fvsCandStamp[c] == fvsScanId ||
                !varsHaveSameType(col, c))
              continue;
            --numDomChecksPredBndAnalysis;
            --numDomChecks;
          }
          domcolFvsCountRemoved.clear();
          from = k;
          if (stop) {
            uncount(k);
            break;
          }
          // a touch, stale signs, or the bound of col now implied: the
          // remaining entries are counted differently, so walk them
          if (domcolFvsTouchEpoch != epoch || domcolSignsDirty ||
              (direction > 0 ? isUpperImplied(col) : isLowerImplied(col))) {
            walkRest = true;
            break;
          }
        }
        domcolFvsCountRow = -1;
        if (!walkRest) return Result::kOk;
        numFvsClosedWalks++;
        uncount(from);
        return walk(from);
      }
      if (!domcolCountPossible || fvsVerify) {
        numFvsWalkScans++;
        return walk(HighsInt{-1});
      }
      // candidates only, in row order
      std::sort(fvsList.begin(), fvsList.end());
      for (HighsInt k : fvsList) {
        if (colDeleted[k]) continue;
        HighsInt pos = findNonzero(row, k);
        if (pos == -1) continue;
        fvsTreat = fvsCandCountOnly[k];
        if (fvsTreat == 0) numFvsOffered++;
        Result result = checkEntry(row, col, pos, direction, bestVal,
                                   hasCliques, false, stop);
        fvsTreat = 0;
        if (result != Result::kOk) return result;
        if (stop) break;
        if (domcolFvsTouchEpoch != epoch || domcolSignsDirty) {
          // a touch: scan-both's scan of the entries after this one
          numFvsFallbacks++;
          const std::vector<HighsInt>& rowpositions = positionsOf(row);
          for (HighsInt rest : rowpositions) {
            if (Avalue[rest] == 0.0 || Arow[rest] != row || Acol[rest] <= k)
              continue;
            HPRESOLVE_CHECKED_CALL(checkEntry(row, col, rest, direction,
                                              bestVal, hasCliques, false,
                                              stop));
            if (stop) break;
          }
          break;
        }
      }
      return Result::kOk;
    };

    // check if bounds are implied or there are cliques
    bool lowerImplied = isLowerImplied(j);
    bool upperImplied = isUpperImplied(j);
    bool hasNegCliques =
        isBinary(j) && mipsolver->mipdata_->cliquetable.numCliques(j, 0) > 0;
    bool hasPosCliques =
        isBinary(j) && mipsolver->mipdata_->cliquetable.numCliques(j, 1) > 0;

    if (fvs) {
      // research (presolve_domcol_first_visit): the two scans of scan-both,
      // in its order, with its conditions
      if (bestRowMinus != -1 &&
          (allowPredBndAnalysis || lowerImplied || hasNegCliques)) {
        size_t p0 = numPairs, r0 = numFixedCols + numModifiedBndsPredBndAnalysis;
        HPRESOLVE_CHECKED_CALL(fvsScan(bestRowMinus, j, HighsInt{-1},
                                       ajBestRowMinus, hasNegCliques,
                                       lowerImplied || hasNegCliques));
        pairsDir[0] += numPairs - p0;
        redsDir[0] += numFixedCols + numModifiedBndsPredBndAnalysis - r0;
      }
      if (!colDeleted[j] && bestRowPlus != -1 &&
          (allowPredBndAnalysis || upperImplied || hasPosCliques)) {
        size_t p0 = numPairs, r0 = numFixedCols + numModifiedBndsPredBndAnalysis;
        HPRESOLVE_CHECKED_CALL(fvsScan(bestRowPlus, j, HighsInt{1},
                                       ajBestRowPlus, hasPosCliques,
                                       upperImplied || hasPosCliques));
        pairsDir[1] += numPairs - p0;
        redsDir[1] += numFixedCols + numModifiedBndsPredBndAnalysis - r0;
      }
    } else if (pairOnce) {
      // research (presolve_domcol_pair_once): direction -1 (minus row) then
      // +1, as below; a list that did not run in full is flagged, and the
      // partners then test those pairs themselves
      uint8_t onceFlags = 0;
      for (HighsInt q = 0; q < 2; ++q) {
        const HighsInt direction = q == 0 ? -1 : 1;
        const HighsInt row = q == 0 ? bestRowMinus : bestRowPlus;
        const double aj = q == 0 ? ajBestRowMinus : ajBestRowPlus;
        const bool cliques = q == 0 ? hasNegCliques : hasPosCliques;
        const bool implied = q == 0 ? lowerImplied : upperImplied;
        bool complete = false;
        if (!colDeleted[j] && row != -1 &&
            (allowPredBndAnalysis || implied || cliques)) {
          size_t p0 = numPairs,
                 r0 = numFixedCols + numModifiedBndsPredBndAnalysis;
          HPRESOLVE_CHECKED_CALL(
              listFromRow(row, j, direction, aj, cliques, false, complete));
          if (!complete) numIncompleteLists++;
          pairsDir[q] += numPairs - p0;
          redsDir[q] += numFixedCols + numModifiedBndsPredBndAnalysis - r0;
        }
        if (!complete) {
          onceFlags |= static_cast<uint8_t>(1 << q);
          // before the switch: pairs j owns in this list are open, and the
          // partners find them only in full scans
          if (onceSwitchCol < 0 && !colDeleted[j] &&
              mirrorLen[2 * j + q] != kHighsIInf) {
            numOnceLost++;
            if (onceLostCol == -1) onceLostCol = 2 * j + q;
            if (onceLostCols.empty() || onceLostCols.back() != j)
              onceLostCols.push_back(j);
          }
        }
      }
      if (!colDeleted[j]) scanFlags[j] = onceFlags;
    } else {
    // which scan to run for row 'row' of sign q (0 minus, 1 plus):
    // 0 = none, 1 = full, 2 = only the pairs whose other column relied on it
    uint8_t flags = 0;
    // ownFix: this column's fixing in this direction is possible (bound
    // implied or cliques); its scan then lists a conclusion its mirror does
    // not, so it is not skipped
    auto scanMode = [&](HighsInt row, HighsInt q, bool useRow,
                        bool ownFix) -> HighsInt {
      if (!mirrorSkip) return useRow ? 1 : 0;
      mirrorStats(row);
      if (useRow && mirrorRows[row].skipped[q] == 0 &&
          mirrorBlockerDeleted(row, q)) {
        mirrorRows[row].stamp = ~size_t{0};
        numMirrorRecomputed++;
      }
      const MirrorRowStats& st = mirrorStats(row);
      if (st.skipped[q] > 0) {
        if (!useRow) numMirrorForced++;
        return useRow ? 1 : 2;
      }
      if (!useRow) return 0;
      if (!ownFix && st.count[1 - q] == 0 && st.notScanned[q] == 0 &&
          (st.maxMirror[q] < rowsize[row] ||
           (st.maxMirror[q] == rowsize[row] && st.maxMirrorCol[q] < j))) {
        flags |= static_cast<uint8_t>(4 << q);
        numMirrorSkipped[q]++;
        return 0;
      }
      return 1;
    };

    // use row 'bestRowMinus'
    HighsInt modeMinus =
        bestRowMinus == -1
            ? 0
            : scanMode(bestRowMinus, 0,
                       allowPredBndAnalysis || lowerImplied || hasNegCliques,
                       lowerImplied || hasNegCliques);
    if (modeMinus != 0) {
      size_t p0 = numPairs, r0 = numFixedCols + numModifiedBndsPredBndAnalysis;
      HPRESOLVE_CHECKED_CALL(checkRow(bestRowMinus, j, HighsInt{-1},
                                      ajBestRowMinus, hasNegCliques,
                                      modeMinus == 2));
      pairsDir[0] += numPairs - p0;
      redsDir[0] += numFixedCols + numModifiedBndsPredBndAnalysis - r0;
    }
    if (modeMinus != 1 || rowDeleted[bestRowMinus]) flags |= 1;

    // use row 'bestRowPlus'
    HighsInt modePlus =
        colDeleted[j] || bestRowPlus == -1
            ? 0
            : scanMode(bestRowPlus, 1,
                       allowPredBndAnalysis || upperImplied || hasPosCliques,
                       upperImplied || hasPosCliques);
    if (modePlus != 0) {
      size_t p0 = numPairs, r0 = numFixedCols + numModifiedBndsPredBndAnalysis;
      HPRESOLVE_CHECKED_CALL(checkRow(bestRowPlus, j, HighsInt{1},
                                      ajBestRowPlus, hasPosCliques,
                                      modePlus == 2));
      pairsDir[1] += numPairs - p0;
      redsDir[1] += numFixedCols + numModifiedBndsPredBndAnalysis - r0;
    }
    if (modePlus != 1 || rowDeleted[bestRowPlus]) flags |= 2;

    // research (presolve_domcol_mirror_skip): record what this column
    // scanned; rows with current statistics are updated here, the others
    // read the flags when recomputed
    if (mirrorSkip && !colDeleted[j]) {
      scanFlags[j] = flags;
      for (const HighsSliceNonzero& nonz : getColumnVector(j)) {
        HighsInt row = nonz.index();
        MirrorRowStats& st = mirrorRows[row];
        if (st.stamp != numMatrixLinks) continue;
        HighsInt q = entrySign(row, nonz.value());
        if (flags & (1 << (1 - q))) {
          st.notScanned[q]++;
          st.notScannedCol[q] = j;
        }
        if (flags & (4 << (1 - q))) st.skipped[q]++;
      }
    }
    }

    // do not use predictive bound analysis if it requires many domination
    // checks and only yields few fixings or improved bounds on average
    size_t averageNumDomChecksPredBndAnalysis =
        numDomChecksPredBndAnalysis / static_cast<size_t>(numCols);
    double averageNumRedsPredBndAnalysis =
        (numFixedColsPredBndAnalysis + numModifiedBndsPredBndAnalysis) /
        static_cast<double>(numCols);
    const bool predWasOn = allowPredBndAnalysis;
    allowPredBndAnalysis =
        allowPredBndAnalysis &&
        (options->presolve_domcol_no_pred_limit ||
         numDomChecksPredBndAnalysis <=
             30 * maxAverageNumDomChecksPredBndAnalysis ||
         (averageNumDomChecksPredBndAnalysis <=
              maxAverageNumDomChecksPredBndAnalysis &&
          averageNumRedsPredBndAnalysis >= minAverageNumRedsPredBndAnalysis));

    // research (presolve_domcol_pair_once): predictive analysis is now off;
    // scan-both would have tested the pairs that visited columns handed to
    // columns not yet visited when it visited them, so test them now, from
    // every visited column whose list ran in full
    if (pairOnce && predWasOn && !allowPredBndAnalysis) {
      onceSwitchCol = j;
      for (HighsInt a = 0; a <= j; ++a) {
        for (HighsInt q = 0; q < 2; ++q) {
          if (colDeleted[a] || (scanFlags[a] & (1 << q))) continue;
          HighsInt row = -1;
          HighsInt rowLen = kHighsIInf;
          double aa = 0.0;
          for (const HighsSliceNonzero& nonz : getColumnVector(a)) {
            if (entrySign(nonz.index(), nonz.value()) != q ||
                rowsize[nonz.index()] >= rowLen)
              continue;
            row = nonz.index();
            rowLen = rowsize[row];
            aa = nonz.value();
          }
          if (row == -1) continue;
          const bool cliques =
              isBinary(a) &&
              mipsolver->mipdata_->cliquetable.numCliques(a, q) > 0;
          bool complete = false;
          HPRESOLVE_CHECKED_CALL(listFromRow(row, a, q == 0 ? -1 : 1, aa,
                                             cliques, true, complete));
          numForcedLists++;
          if (complete && !colDeleted[a])
            scanFlags[a] |= static_cast<uint8_t>(4 << q);
        }
      }
    }
  }

  if (numFixedCols > 0 || numModifiedBndsPredBndAnalysis > 0)
    highsLogDev(options->log_options, HighsLogType::kInfo,
                "Fixed %d dominated columns and strengthened %d bounds\n",
                static_cast<int>(numFixedCols),
                static_cast<int>(numModifiedBndsPredBndAnalysis));
  highsLogDev(options->log_options, HighsLogType::kVerbose,
              "Dominated columns: %d columns, %.0f pairs, %.0f checked, %.0f "
              "domination tests, predictive analysis %s; minus rows %.0f "
              "pairs %.0f reductions, plus rows %.0f pairs %.0f reductions; "
              "%.3f s\n",
              static_cast<int>(numCols), static_cast<double>(numPairs),
              static_cast<double>(numPairsChecked),
              static_cast<double>(numDomChecks),
              allowPredBndAnalysis ? "on" : "off",
              static_cast<double>(pairsDir[0]), static_cast<double>(redsDir[0]),
              static_cast<double>(pairsDir[1]), static_cast<double>(redsDir[1]),
              (timer ? timer->read() : 0.0) - domcolT0);
  highsLogDev(options->log_options, HighsLogType::kVerbose,
              "Dominated columns kinds (-,-) (-,+) (+,-) (+,+): tests %.0f %.0f "
              "%.0f %.0f found %.0f %.0f %.0f %.0f distinct %.0f; mirror "
              "skips minus %.0f plus %.0f forced %.0f col fixings %.0f "
              "recomputed %.0f; pair once prefix lists %.0f incomplete %.0f "
              "moved %.0f lost %.0f (first 2j+q %d) forced %.0f switch col %d "
              "signs dirty %d; tested owned %.0f open %.0f\n",
              static_cast<double>(testsKind[0]),
              static_cast<double>(testsKind[1]),
              static_cast<double>(testsKind[2]),
              static_cast<double>(testsKind[3]),
              static_cast<double>(foundKind[0]),
              static_cast<double>(foundKind[1]),
              static_cast<double>(foundKind[2]),
              static_cast<double>(foundKind[3]),
              static_cast<double>(distinctFound.size()),
              static_cast<double>(numMirrorSkipped[0]),
              static_cast<double>(numMirrorSkipped[1]),
              static_cast<double>(numMirrorForced),
              static_cast<double>(numMirrorFixCol),
              static_cast<double>(numMirrorRecomputed),
              static_cast<double>(numPrefixLists),
              static_cast<double>(numIncompleteLists),
              static_cast<double>(numOnceMoved),
              static_cast<double>(numOnceLost), static_cast<int>(onceLostCol),
              static_cast<double>(numForcedLists),
              static_cast<int>(onceSwitchCol), domcolSignsDirty ? 1 : 0,
              static_cast<double>(numOnceWhy[0]),
              static_cast<double>(numOnceWhy[1]));
  // research (presolve_domcol_first_visit)
  if (fvs)
    highsLogDev(options->log_options, HighsLogType::kVerbose,
                "Dominated columns first visit: offered %.0f tests %.0f "
                "pred checks %.0f (count possible %d); pred scans %.0f fix "
                "scans %.0f full scans %.0f fallbacks %.0f; touched %.0f "
                "extra %.0f pending %.0f used %.0f; degraded %d verify "
                "missed %.0f; closed-form scans %.0f walked scans %.0f "
                "closed-form walk fallbacks %.0f row-cost scans %.0f\n",
                static_cast<double>(numFvsOffered),
                static_cast<double>(testsKind[0] + testsKind[1] +
                                    testsKind[2] + testsKind[3]),
                static_cast<double>(numDomChecksPredBndAnalysis),
                domcolCountPossible ? 1 : 0,
                static_cast<double>(numFvsPredScans),
                static_cast<double>(numFvsFixScans),
                static_cast<double>(numFvsFullScans),
                static_cast<double>(numFvsFallbacks),
                static_cast<double>(domcolFvsNumTouched),
                static_cast<double>(domcolFvsNumExtra),
                static_cast<double>(fvsPendCol.size()),
                static_cast<double>(numFvsPendingUsed),
                domcolSignsDirty ? 1 : 0, static_cast<double>(numFvsMissed),
                static_cast<double>(numFvsClosedScans),
                static_cast<double>(numFvsWalkScans),
                static_cast<double>(numFvsClosedWalks),
                static_cast<double>(numFvsRowScans));

  return Result::kOk;
}

}  // namespace presolve
