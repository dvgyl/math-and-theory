# Formal statement map

The recurrence is a statement about arbitrary functions from the natural numbers to the real numbers. The first required recurrence index is 14. All conclusions begin at index 12.

| Statement | Declaration |
|---|---|
| Literal size seed, quotient seed and all-index recurrence hypotheses | `Motzkin.Forcing.Hypotheses` in `Growth.lean` |
| Simultaneous growth and quotient interval for every n >= 12 | `Motzkin.Forcing.growth_ratio` in `Growth.lean` |
| Exact rational invariant interval and arbitrary normalized-error enclosure | `Motzkin.Forcing.invariant_step` in `Invariant.lean` |
| Full rectangle comparison with the adverse corner | `Motzkin.Forcing.corner_comparison` in `Rectangle.lean` |
| Universal strict corner bound with coefficient 800 | `Motzkin.Forcing.corner_gap` in `Corner.lean` |
| Actual recurrence normalization | `Motzkin.Forcing.local_normalization` in `Forcing.lean` |
| Full robust theorem with cleared denominator | `Motzkin.Forcing.robust_bounded_forcing` in `Forcing.lean` |
| Full robust theorem in the displayed division form, including positivity | `Motzkin.Forcing.robust_bounded_forcing_division` in `Forcing.lean` |
| Exact scaled hypotheses for B >= 0 | `Motzkin.Forcing.ScaledHypotheses` in `Scaling.lean` |
| Corrected scaled growth bound, quotient interval and quartic gap | `Motzkin.Forcing.scaled_bounded_forcing` in `Scaling.lean` |
| Full scaled result in division form, including B = 0 | `Motzkin.Forcing.scaled_bounded_forcing_division` in `Scaling.lean` |

`Certificates.lean` gives exact polynomial identities and their positivity proofs. `Algebra.lean` gives polynomial difference and decomposition identities. A separate statement audit prints the explicit types of all 53 theorem declarations. The last audit imports every proof source and checks their transitive axioms. No theorem treats a finite enumeration as proof of an infinite tail.

The threshold tables, uniform one-parameter root and ratio conclusions, and identification of concrete Motzkin or Riordan sequences are outside this package.
