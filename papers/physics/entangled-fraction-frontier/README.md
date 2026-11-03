# Saturating the steering-centre bound on the fully entangled fraction

**Fully autonomous agentic research.** Autonomous AI research agents found the results, their proofs, the Python checkers and the Lean development in earlier sessions. Opus 5.5 by Anthropic used with Claude Code compared the results with the earlier public record and with this repository's earlier packages, read the central proofs, reran every checker, extended an independent checker, rebuilt the Lean project from source with a whole-project axiom audit, reorganized the manuscript and integrated the package. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Dev D. Goyal · 3 November 2026

## The question

The fully entangled fraction `f(ρ)` of a two-qubit state is its largest overlap with a maximally entangled state; the optimal fidelity of standard teleportation with `ρ` is `(2f+1)/3`. Milne, Jennings, Jevtic and Rudolph, *Quantum correlations of two-qubit states with one maximally mixed marginal* ([arXiv:1404.3951](https://arxiv.org/abs/1404.3951), Phys. Rev. A 90, 024302 (2014)), conjectured (Conjecture 2) that

```
f(ρ) ≤ 1 − c/2,
```

where `c` is the length of the centre of Alice's steering ellipsoid, and that the bound is tight. **That bound is not a result of this package** (see [Prior work and priority](#prior-work-and-priority)). This package asks which states attain it, what it becomes when Bob's marginal is also known, how rigid near-equality is, and what the saturating states look like in every dimension.

## The answer

Write `b` for the length of Bob's Bloch vector and

```
F(c, b) = [√(1+b) + √((1−c)(1−b))]² / 4.
```

- **Sharp joint frontier.** If `b < 1`, then `f(ρ) ≤ F(c, b)`, and every pair `0 ≤ c ≤ 1`, `0 ≤ b < 1` is attained by an explicit state of rank at most two. Since `1 − c/2 − F(c, b) = [√(1−b) − √((1−c)(1+b))]²/4`, the frontier touches `1 − c/2` exactly at `b = c/(2−c)`. At `b = 0` it is Milne et al.'s canonical-state theorem; at `b = 1`, `f = (1+c)/4`.
- **All equality cases.** Each frontier value is attained by exactly one local-unitary orbit. For each `c`, the states with `f = 1 − c/2` form one orbit, represented by `(|χ⟩⟨χ| + c(1−c)|01⟩⟨01|)/(2−c)` with `χ = |00⟩ + (1−c)|11⟩`: pure maximally entangled at `c = 0`, rank two for `0 < c < 1`, pure product at `c = 1`. No full-rank state attains the bound.
- **Optimal stability.** `((2−c)b − c)² ≤ 4(1+√(1−c))² (1 − c/2 − f(ρ))` for every two-qubit state, and the constant is best possible for every `c`.
- **Every dimension.** For a state on `ℂ^d ⊗ ℂ^d` with decreasing marginal spectra `α, β` and a target with decreasing Schmidt amplitudes `s`, `⟨x|ρ|x⟩ ≤ (Σᵢ sᵢ √min(αᵢ, βᵢ))²`, sharply. The states attaining the resulting bound `f_d ≤ (Σᵢ √min(αᵢ, βᵢ))²/d` are exactly a coherent vector plus a positive residual on an explicit rectangle, with no simplicity or rank assumption. This yields maximal Schmidt number, fixed partial-transpose inertia, one-copy distillability, an exact G-concurrence and quasidistillation.
- **Fixed marginals.** An exact reduction of pure-target overlap optimization for arbitrary, possibly singular or rectangular, marginal matrices; a sharp rank bound for every optimizer (`1 + ⌊d²/4⌋` for full-Schmidt square targets); a low-rank optimizer for every target; a unique coherent core.
- **Ellipsoid refinements.** An explicit quartic in signed ellipsoid invariants for the filtering-orbit value, the exact envelope in the centre and the sum of squared semiaxes, low-branch rigidity and the success-probability frontier.
- **Tensor laws.** Every saturator multiplies the Schmidt number of any bipartite second factor: `SN(ρ⊗σ) = r·SN(σ)` with `r = min(rank ρ_A, rank ρ_B)`; full-rank saturators factor both G-concurrence roofs. A rank-three qutrit state with `G = G^a = 3/7` has `G(ω⊗ω) = 0`.
- **Negativity and collective capacity.** Exact negativity optimization on aligned optimal faces, and the exact regularized prescribed-target coupling capacity (`3/5`, `(15+3√21)/50` and `√21/5` in a two-qubit example).

## What is checked, and how

- **Lean** ([lean/](lean/)), Lean 4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. For actual complex matrices: the replayed Omega proof of the known bound (credited); the prescribed-Schmidt bound in every dimension (`MilneExpanded.quantum_overlap_bound`) and its attainer; the qubit frontier `MilneNew.Qubit.fef_frontier_standard`, the bound `(1+c)/4` at `b = 1`, and attaining states for every pair (`MilneNew.Qubit.frontier_sharp`); the stability bound and the optimality of its constant (`MilneNew.Qubit.quantum_stability_coefficient_optimal_closed`); the fixed-marginal reduction; optimizer complementarity, the marginal-rank inequality and the rank ceilings for every optimizer; the matrix identities and the density-matrix properties of the qutrit counterexample; scalar certificates for several further results. The fully entangled fraction is the real supremum over unit vectors with both reduced states `𝟙/2`, and the centre is `(a − Tb)/(1 − b²)`, or `a` when `b = 1`, exactly as in the Omega module. A whole-project audit covers all 620 declarations of the six modules.
- **Not formalized:** the equality classifications, the saturation normal form and its entanglement consequences, low-rank existence, the unique core, the ellipsoid envelopes as statements about states, the tensor laws, the negativity theorems and the asymptotic capacity formula. These are written proofs with exact certificates and numerical checks. [VERIFICATION.md](VERIFICATION.md) states the boundary precisely.
- **Checks** ([analysis/](analysis/), [scripts/](scripts/)): `python3 -I scripts/run_checks.py` replays the 18 exact and numerical checkers and an independent checker from a temporary copy. Floating-point and solver checks detect errors; they are not proofs.

## Prior work and priority

**Earlier public record (note dated 3 November 2026).** The Omega Institute's public repository [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing) records a claimed Lean proof of Conjecture 2, `f(ρ) ≤ 1 − c/2` with an attaining state for every `c`, together with the operator inequality `ρ ⪯ (2−c)(𝟙⊗ρ_B)`; the dossier for issue #14206 was committed on 8 October 2026. This repository's [steering-bounds](../steering-bounds/) package, first committed on 29 October 2026, proves the same bound with sharpness, and [steering-joint-range](../steering-joint-range/) includes those Lean modules unchanged. **I make no priority claim for the bound, its attaining family or the operator inequality.** This package includes a replay of the Omega Lean proof with attribution; its Lean proof bodies are unchanged.

**What is new.** As read on 3 November 2026, the Omega dossier lists the characterization of the equality states and higher-dimensional analogues as open, and neither it nor the two earlier packages contains the joint frontier `F(c, b)`, an equality classification, a stability estimate or any of the higher-dimensional, tensor, negativity or capacity results. A bounded literature search did not find them; this does not establish priority.

**Credited ingredients.** Milne et al. proved the canonical-state value `(1+√(1−c))²/4`, the case `b = 0`. Steering ellipsoids are due to Jevtic, Pusey, Jennings and Rudolph and Milne et al. Klyachko proved the sharp maximal-eigenvalue value `Σ min(αᵢ, βᵢ)` and a low-rank coupling attaining it; the coherent-minimum construction is Wolf's quantum-coupling lemma. The filtering-orbit value is equivalent to a result of Pal, Bandyopadhyay and Ghosh; the purity envelope uses Bravyi's compatibility inequalities; positive equality of the G roofs is characterized by Gour and Guo; classical-residual quasidistillation is due to Baio et al.; coupling capacity is due to Skalski, Todorov and Turowska. The rectangular case of their Theorem 3.7(ii) is corrected in the manuscript; their square-dimensional statements are unaffected. The [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#omega-steering-centre-bounds) gives the dates.

**Third-party code.** `lean/AllProofs.lean` contains the Omega Institute's Lean proof (Apache License 2.0, commit `609e95e`), declarations adapted upstream from `zblore/csd-lean4`, extracts from QICLean and two adapted Mathlib proofs, all under the Apache License 2.0. [lean/THIRD_PARTY_NOTICE.md](lean/THIRD_PARTY_NOTICE.md) records sources and changes, and the license texts are in [lean/third_party/](lean/third_party/).

## Files

- [Manuscript](manuscript.pdf), its [LaTeX source](manuscript.tex), [sections/](sections/) and [figures/](figures/).
- [lean/](lean/): the Lean project. [ProjectAxiomAudit.lean](lean/ProjectAxiomAudit.lean) audits it; [source_manifest.json](lean/source_manifest.json) maps the sections of `AllProofs.lean` to their constituent files.
- [analysis/](analysis/): the 18 checkers, their recorded results, figure scripts and [requirements.txt](analysis/requirements.txt).
- [scripts/](scripts/): the check runner, the independent checker, the axiom-audit checker and [verify.sh](scripts/verify.sh).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
