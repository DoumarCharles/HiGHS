# False `Optimal` from an invalid tableau cut (`HighsTransformedLp::untransform`)

Upstream issue: https://github.com/ERGO-Code/HiGHS/issues/3434

HiGHS reports `Optimal` with primal and dual bound **2467655** on
`highs-tableau-cut-mre.lp`, whose optimum is **2467654**. A cut from the
tableau separator is tightened by 2.1e-5 because `untransform()` drops two
coefficients of size about 1e-11 on columns bounded by 1.8e6 without relaxing
the right-hand side. That cut removes every optimal solution.

The failure is confirmed on:

| commit | build | result |
|---|---|---|
| `3fa5161b1f` (2026-10-15) | Release | `Optimal`, primal = dual = 2467655 (`logs/3fa5161/release-3fa5161.log`) |
| `3fa5161b1f` | Debug + `-DDEBUGSOL=ON` | `checkCut` assertion (`logs/3fa5161/debugsol-3fa5161.log`) |
| `7702861034` (`latest`, 2026-10-16) | Release | `Optimal`, primal = dual = 2467655, with 1 or 2 threads (`logs/latest/`) |

## Files

| file | purpose |
|---|---|
| `highs-tableau-cut-mre.lp` | model: 21 rows, 24 general-integer columns, integer data. sha256 `b6808cff9a66ae1560972b30e01f86ddb174410db70980c882450d506809f228` |
| `opts.txt` | `mip_rel_gap = 0`, `presolve = off`, `threads = 1` |
| `highs-tableau-cut-mre.known.sol` | optimal witness, HiGHS solution format (also usable as `mip_debug_solution_file`) |
| `opts-debugsol.txt` | `opts.txt` plus `mip_debug_solution_file` |
| `verify_optimum.py` | exact rational check of the witness and the lower-bound certificate (standard library only) |
| `logs/` | release and DEBUGSOL logs, gdb scripts and their output, sensitivity runs, diagnostic experiments |

The C++ regression test is `TEST_CASE("issue-3434")` in
`check/TestMipSolver.cpp`, with the model copied to
`check/instances/issue-3434.lp`.

## Reproduce

Run from this directory, with `highs` built from the commit under test.

```
python3 verify_optimum.py highs-tableau-cut-mre.lp highs-tableau-cut-mre.known.sol
highs --options_file opts.txt highs-tableau-cut-mre.lp
```

The first command prints `OPTIMAL VALUE = 2467654`. The second prints
`Status Optimal`, `Primal bound 2467655`, `Dual bound 2467655`.

DEBUGSOL check:

```
cmake -S <HiGHS> -B build-dbg -DCMAKE_BUILD_TYPE=Debug -DDEBUGSOL=ON
cmake --build build-dbg --target highs-bin
build-dbg/bin/highs --options_file opts-debugsol.txt highs-tableau-cut-mre.lp
gdb -batch -x logs/3fa5161/debugsol.gdb --args build-dbg/bin/highs --options_file opts-debugsol.txt highs-tableau-cut-mre.lp
gdb -batch -x logs/3fa5161/untransform.gdb --args build-dbg/bin/highs --options_file opts-debugsol.txt highs-tableau-cut-mre.lp
```

The Release build defines `NDEBUG`, so the DEBUGSOL assertion needs a Debug
build.

Regression test:

```
cmake -S <HiGHS> -B build -DALL_TESTS=ON
cmake --build build --target unit_tests
build/bin/unit_tests "issue-3434"
```

## Proof that the optimum is 2467654

All 19 objective coefficients are 1 and all columns are integer.

1. Fourteen single-variable rows `c·p_k ≥ b_k` give `p_k ≥ ⌈b_k/c⌉`. Together
   these give at least **1,785,174**.
2. `r_23 + r_24 + g_9` gives `10(p_23 + p_24) ≥ 1810157 − 8`. So
   `p_23 + p_24 ≥ ⌈181014.9⌉ = 181,015`.
3. `r_9 + r_10 + r_44 + 3·g_16` gives `20(p_9 + p_10 + p_44) ≥ 10029297`. So
   `p_9 + p_10 + p_44 ≥ ⌈501464.85⌉ = 501,465`.

The lower bound is therefore 1,785,174 + 181,015 + 501,465 = **2,467,654**.

The witness reaches it:
- `x_25 = 4`, `x_26 = 1810153`, `p_23 = 0`, `p_24 = 181015`;
- `x_11 = 3`, `x_50 = 3`, `x_51 = 12`, `p_9 = 154642`, `p_10 = 346823`, `p_44 = 0`;
- every other `p_k` at its minimum from item 1.

It satisfies all bounds and rows in exact arithmetic. Because all three bounds
are tight, every optimal solution has `p_23 + p_24 = 181015`.

## Root cause

`checkCut` fails in the second `generateCut` call of
`HighsTableauSeparator::separateLpSolution` (`HighsTableauSeparator.cpp:237`).

- **Base row.** It is exact: `-p_23 - p_24 + 0.1 s(g_9) + 0.1 s(r_23) + 0.1 s(r_24)`,
  and `checkRowAggregation` passes.
- **Before `untransform`.** The cut has coefficient `0.45000000001164153` on
  `p_23` and `p_24`, and `1.1641534958251043e-11` on the slacks of `r_23` and
  `r_24`.
- **Slack substitution.** Substituting those slacks leaves `-1.16e-11` on
  `x_25` and `x_26`, whose bounds are [0, 1810161].
- **Cleanup.** The non-integral `IsZero` cleanup in
  `HighsTransformedLp::untransform()` reaches this:

  ```cpp
  if (absval <= mip.options_mip_->small_matrix_value) return true;   // dropped, RHS unchanged
  if (absval <= mip.mipdata_->feastol) { ... tmpRhs -= val * bound; ... }  // relaxed
  ```

  Both coefficients are below `small_matrix_value` (1e-9), so they are dropped
  without relaxing the RHS.
- **Resulting cut.** `-0.44999999989522621 (p_23 + p_24) <= -81456.750002107379`,
  that is, `p_23 + p_24 ≥ 181015.0000468`.
  - At the witness its violation is 2.1073e-5, which equals
    `1.1641534958251043e-11 × (x_25 + x_26 = 1810157)`.
  - With the two dropped terms kept, the violation would be 8e-13.
- **False claim.** The root bound rises from 2467653.75 to 2467654.85. It is
  rounded up to 2467655 because the objective is integral, and it meets the
  incumbent.

Diagnostic runs on `3fa5161` (`logs/3fa5161/diagnostic/`):

- **`small_matrix_value = 1e-12`.** The same coefficients now fall into the
  relaxation branch. The result is the correct `Optimal` 2467654, and DEBUGSOL
  raises no assertion.
- **`DIAGNOSTIC-ONLY-not-a-fix.patch`.** Removing the early `return true`
  gives the correct result too. The patch exists only to localise the defect.
  It is not a validated fix: the right general correction, for example how to
  treat tiny coefficients on unbounded columns, needs upstream review.

## Other observations

- **Sensitivity.** The result is unchanged by `random_seed` 1–5,
  `mip_detect_symmetry=false`, `mip_heuristic_effort=0`, feasibility
  tolerances 1e-9 and `simplex_scale_strategy=0` (`logs/3fa5161/matrix/`).
- **Default gap.** With the default `mip_rel_gap`, HiGHS returns 2467655 with
  dual bound 2467654. That is correct within the gap.
- **Presolve on.** This small model solves correctly with presolve on, because
  presolve removes the single-variable rows and the cut is not generated.

## Relation to #3170 and #3171

Both fixes (PRs #3177 and #3179) are in `3fa5161` and `latest`. This failure
differs from both:

- **Separator.** It comes from the tableau separator, not the path separator.
- **No variable bounds.** The model has no binaries, so no variable bounds are
  involved, and no bound type differs between `transform` and `untransform`.
- **Size of the error.** The error is a 2e-5 tightening caused by the
  zero-cleanup step.

## Test evidence (on `latest` 7702861 plus this branch's test)

| run | result | log |
|---|---|---|
| `unit_tests "issue-3434"` | **FAILED**: `REQUIRE( info.mip_dual_bound <= proven_optimum + 1e-6 )` with `2467655.0 <= 2467654.0000009998`. The 120 assertions checking the witness pass. | `logs/latest/unit-test-issue-3434-7702861.log` (the same test before the rename: `unit-test-tableau-cut-untransform-7702861.log`) |
| full `unit_tests` | 439 test cases: 438 passed, 1 failed (only the new test) | `logs/latest/unit-tests-full-7702861.log` |
| new test with the diagnostic patch applied | passed (122 assertions) | `logs/latest/unit-test-tableau-cut-untransform-WITH-DIAGNOSTIC-PATCH.log` |
| `[highs_test_mip_solver]` with the diagnostic patch applied | 65 test cases, all passed | `logs/latest/unit-tests-mip-WITH-DIAGNOSTIC-PATCH.log` |

The patched runs show only that the test detects this defect. They do not
validate the patch as a fix. The branch contains the test only, with no change
to the solver.
