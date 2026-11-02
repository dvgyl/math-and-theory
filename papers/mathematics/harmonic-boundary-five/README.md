# Graphs with five harmonic boundary vertices, subcubic graphs with six, and minimum-boundary two-trees

**Fully autonomous agentic research.** Autonomous AI research agents found the results, their proofs, the finite certificates and an original Lean development in an earlier session; Opus 5.5 by Anthropic used with Claude Code checked the central proofs, reran the checkers, wrote and ran independent enumerations, assembled and audited the Lean project and edited the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

For a connected graph `G`, Steinerberger's boundary `∂G` is the set of vertices `x` for which some vertex `y` satisfies `d(x, y) > (1/deg x) Σ_{z ~ x} d(z, y)`: the distance to `y` is strictly larger at `x` than its average over the neighbours of `x`. Chiem, Dudarov, Lee, Lee and Liu classified the graphs with at most four boundary vertices and asked, as Problem 6.1 of their paper, for the classification of the connected graphs with exactly five.

**Theorem 1 (five boundary vertices).** Every two-connected graph with at most five boundary vertices has diameter at most two (`C_6` shows that five cannot be raised to six). Exactly eighteen two-connected graphs have five boundary vertices: eight of order five and ten of order six. A connected graph has exactly five boundary vertices if and only if it is obtained by independently subdividing bridges of one of **227** reduced graphs, listed in [reduced_kernels_boundary5.g6](checks/experiments/reduced_kernels_boundary5.g6); they have at most fourteen vertices, and one has fourteen.

**Theorem 2 (six boundary vertices, maximum degree three).** Exactly twelve two-connected graphs of maximum degree at most three have six boundary vertices, of order at most ten. A connected graph of maximum degree at most three has exactly six boundary vertices if and only if it is obtained by subdividing bridges of one of **201** reduced graphs, listed in [connected_subcubic_boundary6.g6](checks/extensions/six_boundary/connected_subcubic_boundary6.g6); they have at most eighteen vertices, and two have eighteen.

**Theorem 3 (two-trees).** For `n ≥ 6` every two-tree on `n` vertices has at least `⌈n/2⌉ + 2` boundary vertices, with equality for two graphs at `n = 6`, three at every even `n ≥ 8`, seven at `n = 7`, and, for odd `n ≥ 9` with `r = n mod 8`,

```
a_n = (n⁴ − 20n³ + 239n² + c_r n + d_r)/192,
(c_1, d_1) = (−1126, 2250), (c_3, d_3) = (−1090, 1962), (c_5, d_5) = (−1126, 2298), (c_7, d_7) = (−1090, 1914),
```

so `a_n ~ n⁴/192` over odd `n`. The extremal graphs are described by explicit finite grammars.

The manuscript also proves that in a bipartite graph of maximum degree three the boundary is exactly the set of leaves and vertices on cycles, a sharp rooted truncation theorem for integer metrics, and an infinite family showing that the radius-two local tests used for five points cannot certify realizability for six or more.

## How the proof works and what is checked

The key step for Theorem 1 is the diameter bound. Distances to five designated vertices embed the graph in its distance-profile frame (Müller, Pór and Sereni); the classical three cones of five-point metrics (Koolen, Lesser and Moulton) write the boundary metric with ten half-integer coefficients; two-connectivity forces the five pendant coefficients into `{0, 1/2}`, and a cap that preserves every radius-two local configuration reduces the other five to `{0, 1/2, …, 3}`. An exact local certificate rejects all but fifteen of the 1,613,472 coefficient choices, and the fifteen survivors, which were not changed by the cap, are excluded by hand. Bounded order then follows from the block formula, and a closure computation gives the 227 graphs. For Theorem 2 an all-orders argument shows that the interior of a two-connected core induces a matching or one claw, which bounds its order by fourteen; an exhaustive census of the 60,070 two-connected subcubic graphs of orders six to fourteen then finds the twelve cores.

- [checks/](checks/): the checkers and data (large JSON files are xz-compressed); `python3 checks/run_checks.py --independent` replays them. The `--independent` enumerations were written for this release and share no code with the others: they recompute the 60,070-graph census without nauty, rebuild the 227 and 201 catalogues from their blocks, and compare all graphs of small order with the catalogues and the two-tree formula.
- [lean/](lean/): Lean 4.35.0 proves the degree-three obstruction used in Theorems 1 and 2 at graph level, the block-gluing and accounting identities, the 14-vertex sharpness example, all 835 local infeasibility systems of the certificate, the bipartite boundary theorem, the metric truncation theorem, and the grammar weight bounds and counting identities for Theorem 3. A whole-project audit checks all 15,771 declarations.
- The metric-cone coverage, the capping reduction, the diameter-three argument, the subcubic interior reduction, the block decomposition, the graph-to-grammar correspondence and the catalogue enumerations are conventional proofs and exact computations, not formalized.

## Prior work and priority

The boundary is due to Steinerberger ([Discrete Appl. Math. 338 (2023)](https://arxiv.org/abs/2201.03489)). The question is Problem 6.1 of Chiem, Dudarov, Lee, Lee and Liu, *A characterization of graphs with at most four boundary vertices* ([J. Combin. 15 (2024); arXiv:2209.04438](https://arxiv.org/abs/2209.04438)), whose stability number, bridge rule, degree-two cycle criterion and diameter-two description are used and credited. Theorem 2 and the bipartite theorem bear on their Problem 6.3, which asks when vertices of degree three or four are boundary and what follows for graphs of maximum degree three or four; graphs with six boundary vertices and a vertex of degree at least four remain unclassified. The two-tree theorem and its counting formula answer questions raised in the earlier session rather than in the literature. A literature search in November 2026 found no earlier five-boundary classification; this does not establish priority.

## Files

- [Manuscript](manuscript.pdf), its [LaTeX source](manuscript.tex) with [sections/](sections/) and [figures/](figures/).
- [lean/](lean/): the Lean project; [HarmonicBoundary.lean](lean/HarmonicBoundary.lean) imports every module and [AxiomAudit.lean](lean/HarmonicBoundary/AxiomAudit.lean) audits them.
- [checks/](checks/): finite checkers, catalogues and certificates.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
