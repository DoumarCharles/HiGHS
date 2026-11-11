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
  const bool mirrorSkip = options->presolve_domcol_mirror_skip &&
                          !options->presolve_domcol_pair_once;
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

  // research (presolve_domcol_pair_once): each pair is tested once, when its
  // lower-index column is visited, or later from the other column if that
  // column's list did not run. For y = d x_j, every partner z of y ≻ z has
  // all its negative rows among y's negative rows, so a partner with a
  // negative row is listed by the union of y's negative rows; a partner with
  // none ("free") is listed only by y's shortest positive row. j uses the
  // union when it is shorter and that row has no free entry.
  const bool pairOnce = options->presolve_domcol_pair_once;
  struct SignTrackingGuard {
    HPresolve& presolve;
    ~SignTrackingGuard() { presolve.domcolSignTracking = false; }
  } signTrackingGuard{*this};
  std::vector<HighsInt> pairStamp;
  HighsInt pairVisit = 0;
  struct FreeRowStats {
    HighsInt numFree;
    HighsInt freeCol[2];
    size_t links;
    size_t epoch;
  };
  std::vector<FreeRowStats> freeRows;
  std::vector<std::pair<HighsInt, double>> unionRows;
  size_t numUnionLists = 0;
  size_t numIncompleteLists = 0;
  if (pairOnce) {
    domcolSignCount.assign(2 * static_cast<size_t>(model->num_col_), 0);
    for (HighsInt c = 0; c < model->num_col_; ++c) {
      if (colDeleted[c]) continue;
      for (const HighsSliceNonzero& nonz : getColumnVector(c))
        domcolSignCount[2 * c + entrySign(nonz.index(), nonz.value())]++;
    }
    domcolSignsDirty = false;
    domcolSignTracking = true;
    scanFlags.assign(model->num_col_, 0);
    pairStamp.assign(2 * static_cast<size_t>(model->num_col_), -1);
    FreeRowStats init = {0, {-1, -1}, ~size_t{0}, ~size_t{0}};
    freeRows.assign(model->num_row_, init);
  }
  // entries of the row whose column has no row of the other sign (upper
  // bound: deleted entries stay counted until a recompute)
  auto freeEntries = [&](HighsInt row) -> HighsInt {
    FreeRowStats& st = freeRows[row];
    // a deleted column counted free (it is in no relation any more): the
    // count is recomputed once
    bool freeColDeleted = false;
    for (HighsInt i = 0; i < std::min(st.numFree, HighsInt{2}); ++i)
      freeColDeleted = freeColDeleted || colDeleted[st.freeCol[i]];
    if (st.links == numMatrixLinks && st.epoch == domcolFreeEpoch &&
        !freeColDeleted)
      return st.numFree;
    st.numFree = 0;
    getRowPositions(row, mirror_rowpositions);
    for (HighsInt pos : mirror_rowpositions) {
      if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
      HighsInt c = Acol[pos];
      if (colDeleted[c]) continue;
      if (domcolSignCount[2 * c + 1 - entrySign(row, Avalue[pos])] == 0) {
        if (st.numFree < 2) st.freeCol[st.numFree] = c;
        st.numFree++;
      }
    }
    st.links = numMatrixLinks;
    st.epoch = domcolFreeEpoch;
    return st.numFree;
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

    // increment counter for number of columns
    numCols++;

    // initialise
    HighsInt bestRowPlus = -1;
    HighsInt bestRowPlusLen = kHighsIInf;
    double ajBestRowPlus = 0.0;
    HighsInt bestRowMinus = -1;
    HighsInt bestRowMinusLen = kHighsIInf;
    double ajBestRowMinus = 0.0;
    // research (presolve_domcol_pair_once): total length of j's rows of each
    // sign
    int64_t sumLenPlus = 0;
    int64_t sumLenMinus = 0;

    for (const HighsSliceNonzero& nonz : getColumnVector(j)) {
      HighsInt row = nonz.index();
      HighsInt scale = model->row_upper_[row] != kHighsInf ? 1 : -1;

      double val = scale * nonz.value();
      if (val > 0.0) sumLenPlus += rowsize[row];
      if (val < 0.0) sumLenMinus += rowsize[row];
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
        // increment counter for number of domination checks due to predictive
        // bound analysis
        if (!tryToFix && !tryToFixCol) numDomChecksPredBndAnalysis++;
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
                             double ak, bool hasCliques) {
      if (k == col || colDeleted[k]) return Result::kOk;
      // a visited k listed this pair in its scan of sign -dirK unless that
      // scan did not run in full
      if (k < col && !(scanFlags[k] & (1 << (dirK > 0 ? 0 : 1))))
        return Result::kOk;
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
      if (!checkDominationNonZero(row, direction * aj, dirK * ak))
        return Result::kOk;
      return checkCols(row, col, k, direction, direction * dirK, boundImplied,
                       hasCliques, sameVarType, true, false, kImplied,
                       kCliques);
    };

    // research (presolve_domcol_pair_once): list the partners of direction
    // * x_col from its shortest row of that sign; complete = every partner
    // was offered
    auto listFromRow = [&](HighsInt row, HighsInt col, HighsInt direction,
                           double aj, bool hasCliques, bool& complete) {
      complete = false;
      if (rowDeleted[row]) return Result::kOk;
      const std::vector<HighsInt>& rowpositions = positionsOf(row);
      for (HighsInt pos : rowpositions) {
        if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
        HighsInt k = Acol[pos];
        HPRESOLVE_CHECKED_CALL(checkPairOnce(row, col, k, direction, direction,
                                             aj, Avalue[pos], hasCliques));
        if (colDeleted[col] || rowDeleted[row]) return Result::kOk;
        if (colDeleted[k] || Avalue[pos] == 0.0 || Arow[pos] != row) continue;
        HPRESOLVE_CHECKED_CALL(checkPairOnce(row, col, k, direction,
                                             -direction, aj, Avalue[pos],
                                             hasCliques));
        if (colDeleted[col] || rowDeleted[row]) return Result::kOk;
      }
      complete = true;
      return Result::kOk;
    };

    // research (presolve_domcol_pair_once): list them from all rows where
    // direction * x_col is negative; a partner dirK * x_k is offered from a
    // row where it is negative too, once
    auto listFromUnion = [&](HighsInt col, HighsInt direction,
                             bool hasCliques, bool& complete) {
      complete = false;
      unionRows.clear();
      for (const HighsSliceNonzero& nonz : getColumnVector(col))
        if (entrySign(nonz.index(), nonz.value()) == (direction > 0 ? 0 : 1))
          unionRows.emplace_back(nonz.index(), nonz.value());
      ++pairVisit;
      const size_t links0 = numMatrixLinks;
      const size_t epoch0 = domcolFreeEpoch;
      for (const std::pair<HighsInt, double>& r : unionRows) {
        HighsInt row = r.first;
        if (rowDeleted[row]) continue;
        const std::vector<HighsInt>& rowpositions = positionsOf(row);
        for (HighsInt pos : rowpositions) {
          if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;
          HighsInt k = Acol[pos];
          if (k == col || colDeleted[k]) continue;
          HighsInt dirK = entrySign(row, Avalue[pos]) == 1 ? -1 : 1;
          size_t slot = 2 * static_cast<size_t>(k) + (dirK > 0 ? 1 : 0);
          if (pairStamp[slot] == pairVisit) continue;
          pairStamp[slot] = pairVisit;
          HPRESOLVE_CHECKED_CALL(checkPairOnce(row, col, k, direction, dirK,
                                               r.second, Avalue[pos],
                                               hasCliques));
          if (colDeleted[col] || rowDeleted[row]) return Result::kOk;
        }
      }
      // rows and signs unchanged: no partner can have become free
      complete = numMatrixLinks == links0 && domcolFreeEpoch == epoch0 &&
                 !domcolSignsDirty;
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
      for (HighsInt pos : *rowpositions) {
        if (Avalue[pos] == 0.0 || Arow[pos] != row) continue;

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

    if (pairOnce) {
      // research (presolve_domcol_pair_once): direction -1 (minus row) then
      // +1, as below; a list that did not run in full is flagged, and the
      // later partners then test those pairs themselves
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
          // rows where direction * x_j is negative
          const int64_t unionLen = q == 0 ? sumLenPlus : sumLenMinus;
          size_t p0 = numPairs,
                 r0 = numFixedCols + numModifiedBndsPredBndAnalysis;
          if (!domcolSignsDirty && unionLen < rowsize[row] &&
              freeEntries(row) - (unionLen == 0 ? 1 : 0) == 0) {
            numUnionLists++;
            HPRESOLVE_CHECKED_CALL(
                listFromUnion(j, direction, cliques, complete));
          } else {
            HPRESOLVE_CHECKED_CALL(
                listFromRow(row, j, direction, aj, cliques, complete));
          }
          if (!complete) numIncompleteLists++;
          pairsDir[q] += numPairs - p0;
          redsDir[q] += numFixedCols + numModifiedBndsPredBndAnalysis - r0;
        }
        if (!complete) onceFlags |= static_cast<uint8_t>(1 << q);
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
    allowPredBndAnalysis =
        allowPredBndAnalysis &&
        (options->presolve_domcol_no_pred_limit ||
         numDomChecksPredBndAnalysis <=
             30 * maxAverageNumDomChecksPredBndAnalysis ||
         (averageNumDomChecksPredBndAnalysis <=
              maxAverageNumDomChecksPredBndAnalysis &&
          averageNumRedsPredBndAnalysis >= minAverageNumRedsPredBndAnalysis));
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
              "recomputed %.0f; pair once union lists %.0f incomplete %.0f "
              "signs dirty %d\n",
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
              static_cast<double>(numUnionLists),
              static_cast<double>(numIncompleteLists),
              domcolSignsDirty ? 1 : 0);

  return Result::kOk;
}

}  // namespace presolve
