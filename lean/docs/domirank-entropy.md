# DomiRank entropy counterexample

[Paper](../../preprints/domirank-entropy/paper.pdf) · [Computation](../../verification/domirank-entropy/README.md) · [Central verification](../../verification/README.md)

## Source and exact scope

The source is [Zhang and Zhao, arXiv:2610.00107v4](https://arxiv.org/html/2610.00107v4), dated 15 October 2026. Conjecture 4.9 asserts decreasing entropy on every positive-score interval in the stable domain when the degree–log-degree edge covariance is nonpositive. It does not restrict the assertion to the first connected component of the positive-score set.

The fixed graph has 14 vertices and 32 edges. Its covariance is negative. Its actual resolvent scores are positive throughout `[251/1000,63/250]`. The entropy increases by more than `1/10000` in natural-logarithm units. The proof therefore addresses the refined conjecture. The source's earlier positive-covariance example addresses a different hypothesis.

## Formal correspondence

The [Challenge](../Challenges/DomiRank.lean) specifies the graph by edge rules. It defines adjacency, degrees, covariance, inverse-matrix scores, normalization, and Shannon entropy independently. The [Solution](../Solutions/DomiRank.lean) proves equality with the library objects, including a finite check of the graph adjacency. It does not assume a spectral estimate or a probability identity.

All substantive declarations below use namespace `MathAndTheory.DomiRank`.

| Mathematical obligation | Declaration |
|---|---|
| Graph and matrix agree | `A_eq_adjMatrix`, `degree_eq_graph_degree` |
| Graph is connected | `graph_connected` |
| Negative source covariance | `degreeLogCovarianceBits_neg` |
| Positive-definite resolvent on the interval | `resolvent_posDef_on_interval` |
| Stable spectral-domain inequality | `spectral_bound_on_interval` |
| Actual inverse scores and positivity | `gamma_eq_candidate`, `gamma_pos_on_interval` |
| Positive-part and source normalizations agree | `distribution_eq_theoretical` |
| Strict rational entropy gap | `entropyNats_gap` |
| Source entropy in bits increases | `theoretical_entropy_strict_increase` |
| Complete graph witness | `fourteen_vertex_counterexample` |

The [Comparator configuration](../comparator/domirank-entropy.json) selects `DomiRankProblem.counterexample`. Natural logarithms change entropy and covariance by the positive factor `log 2`. The formal development proves the source's base-two entropy comparison as well.

## Prior work and limits

The source's current version, its initial derivative calculation, unconditional example, refined conjecture, and exact normalization were inspected. Searches used the source identifier, entropy, covariance, positive-score intervals, and alternative centrality terminology. No earlier counterexample to the refined interval statement was identified. The pinned Mathlib and formal-conjectures trees had no matching target. Public database queries did not provide an exhaustive citation search. No priority claim follows from these searches.

This is a theorem about the stated mathematical centrality model. It does not establish empirical performance on networks. It does not refute a narrower assertion restricted to an initial positive component. No human expert peer review is claimed.
