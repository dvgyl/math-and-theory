# ECQC formal statement map

All scientific declarations below are in namespace `ECQC5`. The source package pins Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Exact models

- `Q = Fin 5` indexes the five outcomes. `QQ = Q × Q` indexes the bipartite computational basis. Finite arithmetic matches the paper's field-index computations modulo five.
- `zeta` is the actual complex exponential `exp (2*pi*I/5)`, not an abstract symbol assumed to have root identities.
- `psi` is the normalized vector with coefficient `1/sqrt(5)` when Bob's index is twice Alice's index modulo five. `rho` is its actual outer-product matrix. `rhoA` and `rhoB` are explicit partial traces.
- `vonNeumannEntropy` is minus the real part of the trace of the continuous functional calculus of `t*log t`. The conventional zero-eigenvalue contribution is zero.
- `measurementVec b k x` is the coefficient of basis vector `k` at computational coordinate `x`. A setting is `Option Q`: `none` is the computational basis, and `some a` is the quadratic basis with exponent `a*x²+k*x`.
- `basisMatrix` has these vectors as columns. `bornAmplitude` contracts the same setting's actual basis vectors with `psi` on both parties. This is the paper's identical-local-basis convention; Bob does not use a separately conjugated basis family.
- `bornProb` is the squared complex norm of that amplitude. `tableZ i j` is `1/5` when `j=2*i`, and zero otherwise. `classicalMI` is the Shannon mutual information of the actual row, column, and joint distributions. `actualScore S` sums the actual measurement mutual information over a five-setting finite subset.

## Main claims and supporting declarations

| Manuscript claim | Exact declaration | Source module |
|---|---|---|
| Theorem 1, complete physical counterexample | `pure_state_ECQC_counterexample` | `Main.lean` |
| No allowed five-setting budget | `no_actual_five_setting_budget` | `Main.lean` |
| Strict violation after conversion to bits | `actualScore_bits_violation` | `Main.lean` |
| Unit state vector | `psi_norm` | `Foundation.lean` |
| Positive trace-one pure density matrix | `rho_positive`, `rho_trace`, `rho_idempotent` | `Foundation.lean` |
| Both partial traces equal identity divided by five | `rhoA_diagonal`, `rhoB_diagonal` | `Foundation.lean` |
| Quantum mutual information equals `2 log 5` | `quantumMI_eq` | `Foundation.lean` |
| Every measurement matrix is unitary | `bases_unitary` | `Main.lean` |
| Every pair of distinct settings is mutually unbiased | `bases_mutually_unbiased` | `Main.lean` |
| Exact actual Born table, equation (4) | `bornProb_eq_table` | `Main.lean` |
| Actual table is normalized and nonnegative | `bornProb_normalized`, `bornProb_nonneg` | `Main.lean` |
| Every actual classical mutual information equals `log 5` | `bornProb_classicalMI` | `Main.lean` |
| Every allowed five-setting selection has score `5 log 5` | `actualScore_eq` | `Main.lean` |

`Raw.lean` proves the fifth-root sums, raw quadratic overlaps, and raw Born identity. `Entropy.lean` proves the permutation table's marginals, Shannon entropies, mutual information, and existence of a five-setting subset. `Main.lean` connects these results to the normalized bases and actual Born probabilities. The final theorem includes density-matrix positivity, trace one, purity, six settings, unitarity, unbiasedness, exact table equality, quantum mutual information, existence of an allowed selection, and the strict inequality for **every** allowed selection.

The paper's minimum score follows because five-setting selections exist and all of them have the same sum. The formal statement does not silently replace an optimized choice by a selected example. It proves that no permitted selection satisfies the proposed budget.

## Checking and its limits

The five scientific proof files match the checked inputs. The 28 October 2026 build and `--trust=0 ReplayAudit.lean` audit succeeded. The audit requires exactly these eight reports:

```text
ECQC5.pure_state_ECQC_counterexample
ECQC5.no_actual_five_setting_budget
ECQC5.actualScore_bits_violation
ECQC5.bases_unitary
ECQC5.bases_mutually_unbiased
ECQC5.bornProb_eq_table
ECQC5.quantumMI_eq
ECQC5.rho_positive
```

All contain only `propext`, `Classical.choice`, and `Quot.sound`. Reproduction commands are in the README. Formal success does not establish the literal contents or currency of the motivating papers, historical priority, experimental realization, expert validation, or external conjecture identity.

## Conventional all-prime companion

The companion [prime-family-proof.md](../prime-family-proof.md) proves the same fixed-family, identical-local-basis score formula for every prime p congruent to 1 modulo 4. Its ratios p/2 are unbounded. That extension is a conventional proof. The Lean project formalizes dimension five only. Neither result optimizes over other MUB collections or local basis changes.
