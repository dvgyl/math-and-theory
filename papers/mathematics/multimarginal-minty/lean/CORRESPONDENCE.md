# Manuscript-to-Lean correspondence

This file maps the claims of the manuscript (`../manuscript.tex`) to formal declarations. Lean uses the coordinate carrier `Fin 2 -> R`; its `pairing` is explicitly the ordinary Euclidean dot product. The carrier's unrelated default function-space norm is never substituted for the Euclidean pairing. `Minty.pairing_eq_euclidean_inner` connects it to mathlib's `EuclideanSpace R (Fin 2)`.

| Manuscript obligation | Lean declaration(s) | Scope and edge cases |
|---|---|---|
| Real plane, three marginals, quadratic cost and coordinate mixing | `Vec`, `Triple`, `pairing`, `total`, `cost`, `mix` in `Minty/Core.lean` | Arbitrary real coordinates; all three marginals. |
| Actual two-point cost-swap monotonicity | `CMonotone` | Quantifies over every pair in an arbitrary set and every `Finset (Fin 3)`, including empty and full subsets. |
| Genuine inclusion maximality | `MaximalCMonotone` | Quantifies over every containing subset of the full ambient space, without finiteness, domain or regularity restrictions. |
| Equivalence with three singleton cuts | `compatible_iff_swaps`, `cMonotone_iff_compatible` | All eight membership masks are handled; complementary cuts are not silently omitted. |
| Explicit three-element seed | `witness`, `seed`, `witness_injective`, `seed_ncard` | Finite real-coordinate data; distinctness and cardinality three explicitly proved. |
| Every seed pair satisfies monotonicity | `witness_compatible`, `seed_cMonotone` | All ordered pairs, identical pairs and every singleton; cost-swap equivalence supplies all subsets. |
| Exact sum-of-squares identity | `planar_certificate_identity` | Equality for every four real variables, verified by ring normalization. |
| Four necessary inequalities are inconsistent with sum zero | `planar_polynomial_obstruction` | Six arbitrary real variables, both sum constraints and the four nonpositive inequalities. |
| No actual compatible tuple has sum zero | `no_zero_extension` | Extracts the four necessary inequalities from the actual `Compatible` relation; no rational/grid restriction or assumed solver certificate. |
| Every c-monotone seed superset excludes zero from its sum image | `zero_not_total_image_of_seed_subset` | Actual set image `total '' S`; all real tuples in arbitrary supersets. |
| Chain unions preserve c-monotonicity | `cMonotone_sUnion` | Any chain; each pair lies in a common chain member. |
| A globally maximal extension exists | `exists_maximal_extension` | Formal Zorn argument on all monotone supersets, followed by unrestricted ambient maximality. |
| Every containing sum image is nonconvex | `total_image_not_convex_of_seed_subset` | Uses exact positive convex weights 28, 173, 205 (total 406) and the zero-exclusion theorem. |
| Complete maximal-set counterexample | `exists_maximal_cMonotone_nonconvex_sum` | Actual maximal set, seed containment, excluded zero, and actual failure of `Convex R` in one theorem. |
| Negation of the published universal implication | `not_all_maximal_cMonotone_have_full_sum` | Refutes the universal full-sum assertion already at fixed N=3 and H=R2. |
| Euclidean rather than accidental norm convention | `euclideanEquiv`, `pairing_eq_euclidean_inner` | Coordinate pairing equals the ordinary Hilbert inner product under the explicit equivalence. |

## What the formal claim does not include

The theorem is for three marginals on the real plane. The manuscript does not assert a classification for all marginal counts/dimensions, dimension minimality, full cyclic monotonicity, splitting potentials, closedness of the sum image, or a quantified omitted open ball. Higher-dimensional embeddings are not substituted for formally verified general endpoints.

Section 4's firmly nonexpansive-map interpretation is an ordinary mathematical consequence, shown in the manuscript by the sum-injectivity and norm-square inequalities. The formal development encodes the equivalent finite relations and the complete maximality theorem; it does **not** separately package the partial maps as mathlib functions with a named `FirmlyNonexpansive` predicate. This distinction is explicit and does not weaken the formal main theorem.

The positive numbers `23/26`, `(4,3,4,8)` and the witness coordinates are exact rational/integer constants inside real arithmetic. A numerical search suggested the construction, but its output and solver status are absent from the formal hypotheses. The standard-library Python checker is a separate reproducibility aid, not a replacement for Lean's proof of arbitrary-real infeasibility and Zorn existence.

The independent review identified the initially unstated cardinality lemma; `witness_injective` and `seed_ncard` were then added before the final source snapshot and rebuild. No prior theorem statement was weakened to make compilation pass. Exact final hashes, compile commands and transitive axiom counts belong to `FORMAL_VERIFICATION.md` and its logs.
