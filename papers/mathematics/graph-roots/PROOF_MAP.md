# Claim and proof map

The main graph F_(4,n) consists of n distinct four-cycles sharing exactly one vertex. Books B_n share an edge. Neither is identified with the triangular friendship family.

| Manuscript claim | Complete conventional argument | Boundaries |
|---|---|---|
| Lemma 1: flower polynomial and zero multiplicity | Independent counting with/without the common vertex; H_n(0)=0 and H_n'(0)=3^n+3n>0 | Every n≥1; exactly n+1 zero roots and 2n nonzero roots counting multiplicity; R_n>0 |
| Theorem 2: all-n upper bound | Root factor estimate for A(z), normalized root equation, ylogy inversion by positive real W | r≥3 treated directly; remaining roots including0 covered because upper bound exceeds 3 |
| Theorem 2: sharp escape law | Complex Lambert fixed point, exact reciprocal identity, uniform logarithmic perturbation, Rouché root, additive reciprocal-square error, matching upper bound | Actual roots for all sufficiently large n; principal logarithm restricted to right half-plane; analytic denominators nonzero; v_n→0 proved |
| Proposition 3: flower real roots | Exclusion outside1<t<2; odd-index sign; n=2 identity; two monotone subintervals and positive middle interval | Odd n and n=2 have only0; even n≥4 have exactly two simple nonzero roots in stated intervals |
| Proposition 4: root movement and first-order asymptotics | Positive F_(n+2)−F_n; endpoint limits; bounded y=ns and mean-value estimate | Even n≥4; constants log(phi) and log2; errors O(n^-2) |
| Proposition 5: books | Independent counting; logarithmic derivative; interval exclusions; monotone K_n; strict convexity with exact negative witnesses | n=1 exception; even/odd classifications; zero multiplicity2; all nonzero real roots simple |

The positive real Lambert W function is defined by its inverse equation. The complex fixed point is constructed rather than assumed from a branch label. The proof retains additive o(1) precision: the constructed root differs in reciprocal-square scale by at most2|v_n|+|v_n|²/|lambda_n|; the upper-bound shift contributes O(W(4n)^(3/2)/sqrt(n))=o(1).

## Computational scope

The supplied finite records enumerate 948,704 vertex subsets, verify Sturm counts through 20, and give numerical diagnostics. They are corroboration, not the all-n proof. No numerical root is certified as the maximum solely from its residual. The new checker wrapper rejects optimized Python; its arithmetic body is byte-identical to the original. The five startup modes are tested without enumeration.

## Formal coverage

The [portable package](formalization/README.md) contains the complete source closure. Its [theorem map](formalization/THEOREMS.md) identifies the checked endpoints for all numbered manuscript conclusions.

The main escape theorem has a complete Lean development for the actual finite square-flower graph. Fresh kernel replays and explicit theorem-type and transitive-axiom audits cover its counting, analytic construction, radius bounds, and final limits. Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. Accepted proof dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.

| Formal claim | Endpoint in namespace `SquareFlowerCompletion` |
|---|---|
| Combined main escape theorem | `Extremal.main_escape_theorem` |
| Actual graph domination-subset counting identity | `Counting.dominationPolynomial_formula` |
| Degree 3n+1 and origin multiplicity n+1 | `Extremal.graphPolynomial_natDegree`, `Extremal.graphPolynomial_origin_multiplicity` |
| Nonempty complete nonzero root set for n≥1 | `Extremal.nonzeroRootFinset_nonempty` |
| Positive radius and exact maximum over all nonzero roots | `Extremal.radius_pos`, `Extremal.radius_eq_nonzero_max` |
| Constructed actual roots with additive reciprocal-square precision | `Transfer.exists_actual_graph_roots_with_scale` |
| Original strict bound for every n≥1 | `Extremal.radius_strict_global_bound` |
| Additive law 4n/R_n²−log(4n)+log(log(4n))→0 | `Extremal.radius_reciprocal_square_asymptotic` |
| Leading equivalent R_n/(2sqrt(n/log n))→1 | `Extremal.radius_leading_equivalent` |

The formal root transfer uses explicit derivative estimates and a contraction on a complete closed disk. This method proves the same eventual actual roots and additive precision as the manuscript's Rouché step. The final squeeze uses a proved shifted-three auxiliary bound with a vanishing additive shift error. The original sharper shifted-two bound is also proved separately for every positive order.

The continuation sources cover Propositions 3–5. EvenRoots.lean and EvenSimplicity.lean prove the flower classification and actual polynomial simplicity. RootMotion.lean proves strict motion and endpoint limits. RootEndpointExpansion.lean proves the original log(phi)/n and log(2)/n expansions with explicit O(n^-2) bounds. NonzeroRootCount.lean proves the exact 2n nonzero complex-root count with multiplicity.

BookGraph.lean through BookPolynomial.lean define the actual book graph and prove its domination-subset formula. BookOrigin.lean proves origin multiplicity two and the n=1 exception. BookRootClassification.lean proves the full even/odd classification, nonzero real-root simplicity over both coefficient fields, and exactly four real roots counted with multiplicity for n≥2. The n=0 single-edge case has a separate formula. No formal claim is inferred from finite checks.

The conclusions of all numbered manuscript results are covered by the 70-module package. Its 258 explicit statement and final axiom reports include the main theorem and the companion proof endpoints. This coverage does not claim that every intermediate prose calculation has a separate formal counterpart.

## Novelty boundary

The complete complex zero set or a limiting curve is not classified. No specifically numbered conjecture is declared resolved. The source notation F_n versus F_(4,n), source chronology, and equivalent earlier asymptotic results still need primary-source review. Reference metadata and source correspondence remain provisional.
