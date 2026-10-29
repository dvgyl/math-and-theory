# Formal theorem map

`SquareFlowerCompletion.Counting.flower n` is the simple graph of n squares sharing one vertex. `BookCompletion.book n` has two hubs, their common edge, and n distinct paths of length three between the hubs. Both domination polynomials sum over actual dominating subsets. Their formulas are theorems.

| Manuscript conclusion | Formal endpoint or source |
|---|---|
| Flower counting formula | `SquareFlowerCompletion.Counting.dominationPolynomial_formula` in FlowerPolynomial.lean |
| Flower degree and origin multiplicity | `SquareFlowerCompletion.Extremal.graphPolynomial_natDegree`, `graphPolynomial_origin_multiplicity` in GraphDegree.lean |
| Exactly 2n nonzero complex roots with multiplicity | `SquareFlowerCompletion.Extremal.nonzero_root_multiset_card` in NonzeroRootCount.lean |
| Positive maximum over the complete nonzero root set | `SquareFlowerCompletion.Extremal.radius_pos`, `radius_eq_nonzero_max` in NonzeroRoots.lean |
| Main escape theorem and original strict all-n bound | `SquareFlowerCompletion.Extremal.main_escape_theorem` in MainTheorem.lean; `radius_strict_global_bound` in SharpRadius.lean |
| Additive reciprocal-square law and leading equivalent | `SquareFlowerCompletion.Extremal.radius_reciprocal_square_asymptotic`, `radius_leading_equivalent` |
| Positive exclusion, confinement, odd-order and n=2 exceptions | RealExclusions.lean |
| Two even-order nonzero real roots in the stated intervals | `SquareFlowerCompletion.RealCompanion.even_order_real_root_classification` in EvenRoots.lean |
| Actual polynomial multiplicity-one simplicity | `SquareFlowerCompletion.RealCompanion.even_nonzero_real_root_multiplicity_one` in EvenSimplicity.lean |
| Strict even-order motion and endpoint limits | RootMotion.lean |
| Original endpoint coefficients and O(n^-2) errors | `SquareFlowerCompletion.RealCompanion.leftCoordinate_endpoint_error`, `rightCoordinate_endpoint_error`, `even_leftCoordinate_endpoint_expansion`, `even_rightCoordinate_endpoint_expansion` in RootEndpointExpansion.lean |
| Book formula, including separate n=0 formula | `BookCompletion.dominationPolynomial_formula`, `dominationPolynomial_zero` in BookPolynomial.lean |
| Book origin multiplicity two for n≥1 and n=1 exception | `BookCompletion.realPolynomial_origin_multiplicity`, `realPolynomial_one_roots` in BookOrigin.lean |
| Book even n≥2 classification and real/complex simplicity | `BookCompletion.book_even_real_roots` in BookRootClassification.lean |
| Book odd n≥3 classification and real/complex simplicity | `BookCompletion.book_odd_real_roots` in BookRootClassification.lean |
| Book exactly four real roots counted with multiplicity, n≥2 | `BookCompletion.book_real_roots_card` in BookRootClassification.lean |

StatementAudit.lean prints the explicit types of the 258 audited declarations. CompleteAudit.lean prints the transitive axiom dependencies for those same declarations. Its import closure contains every scientific source in sources.json.

The formal complex-root construction uses explicit derivative estimates and contraction on a complete closed disk. It proves the same eventual-root and additive-precision conclusions as the manuscript's Rouché argument. The endpoint sequences use n=2k+4 to state limits and error bounds through even orders. Auxiliary transformed roots at odd orders are not identified as flower roots.

All numbered manuscript conclusions are covered. Formal verification does not establish novelty, source chronology, bibliography accuracy, or a classification of the full complex zero set. It does not assert that every complex book root is simple.
