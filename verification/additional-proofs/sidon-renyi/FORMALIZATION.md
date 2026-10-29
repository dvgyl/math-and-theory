# Formal statement map

All declarations below are in namespace `SidonRenyi`. The source package pins Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

| Informal claim | Formal declaration | Module |
|---|---|---|
| Complete order classification, Theorem 1 | `universalUniformOptimal_iff_criticalOrder` | `Main.lean` |
| Exact scalar criterion | `universalUniformOptimal_iff` | `Main.lean` |
| Arbitrary-support entropy inequality | `renyiSumEntropy_le_uniform` | `Main.lean` |
| Strict binary entropy counterexample | `exists_binary_entropy_counterexample` | `Main.lean` |
| Uniform entropy value, equation (1) | `renyiSumEntropy_uniform_value` | `Main.lean` |
| Actual convolution equals the moment formula | `iidConvolution_powerMoment` | `SidonLaw.lean` |
| Convolution is nonnegative and normalized | `iidConvolution_nonneg`, `sum_iidConvolution_eq_one` | `SidonLaw.lean` |
| Sharp power comparison, Lemma 2 | `power_difference_lt` | `PowerDifference.lean` |
| Coordinate order of the gradient, Lemma 3 | `momentGradient_lt`, `momentGradient_mono` | `Gradient.lean` |
| Global minimum including zero coordinates, Proposition 4 | `powerMoment_uniform_le` | `Optimization.lean` |
| Critical root and interval classification | `criticalOrder_bounds`, `criticalOrder_equation`, `exists_unique_criticalOrder`, `criticalOrder_condition_iff` | `Threshold.lean` |

`IsSidonMap` includes repeated indices. The entropy definition uses the finite convolution `iidConvolution`, summed over `sumSupport`; it is not merely an assumed distribution on unordered pairs. The universal predicate quantifies over finite nonempty supports in abelian groups. The forward inequality also applies to a commutative additive semigroup and is universe-polymorphic.

The public theorem is for orders greater than one and uses natural logarithms. It makes no Shannon-entropy claim at one and no equality-case uniqueness claim. The abstracted moment, literal probability law, and logarithmic entropy are linked by formal theorems.

To reproduce the checks, follow the README commands. `AxiomAudit.lean` prints the definitions, main theorem types, and transitive axiom dependencies of twelve declarations. `verify.sh` now checks report coverage with `check_axioms.py`, requires one report for each of those twelve declarations, and rejects malformed, duplicate, missing, or unexpected reports. A failed Lake command retains its exit code. The accepted dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. Compilation establishes the checked proposition; source fidelity, historical novelty, and peer review remain separate questions.

A fresh Lean 4.19.0 build and wrapper audit succeeded on 28 October 2026. A separate audit with `--trust=0` also succeeded and accepted all twelve named declarations with only the permitted axioms. All twelve Lean source files remained unchanged and match these sources. These are fresh compiler results, distinct from the earlier supplied build records and from parser-only failure controls.
