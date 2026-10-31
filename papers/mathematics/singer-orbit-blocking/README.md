# Blocking sets of PG(2,13) invariant under a fixed-point-free Singer subgroup meet some line in five points

**Fully autonomous agentic research.** Autonomous AI research agents selected the question, found the reduction, identified the matching example and produced a solver certificate; Opus 5.5 by Anthropic used with Claude Code wrote the Lean proof used here, including a kernel-checked search with a soundness proof, wrote an independent exact checker, ran a fresh Lean build and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Erdős Problem [#1159](https://www.erdosproblems.com/1159) asks whether there is a constant `C` such that every finite projective plane has a point set meeting every line in at least one and at most `C` points. For a single plane this is the question of the least possible largest line intersection of a blocking set. In `PG(2,13)` the 21-point blocking set of Blokhuis, Brouwer and Wilbrink (2003, Section 5.3) meets every line in at most five points. A [public computational campaign](https://github.com/pw/erdosproblemaday-verification/blob/7bccace07c6b555623be274558e463b5ef2c3ea1/1159/1159-klein-blocks-pg2-11-and-the-q13-question/orbitzoo/orbitzoo_q13.log) looked for blocking sets of `PG(2,13)` with all line intersections at most four that are invariant under various collineation groups; for the subgroup of order three of a Singer group, with 61 orbits of size three, its solver stopped with status UNKNOWN after 90 seconds.

Let `θ` be a root of `X³ + X + 6` over `F₁₃`, let `σ` be the Singer cycle of `PG(2,13)` induced by multiplication by `θ` on `F₁₃[θ] = F₁₃³`, and let `H = ⟨σ⁶¹⟩`, a subgroup of order three without fixed points.

**Theorem.** Every `H`-invariant blocking set of `PG(2,13)` meets some line in at least five points. The image of the Blokhuis–Brouwer–Wilbrink set, the union of seven `H`-orbits, is an `H`-invariant minimal blocking set of 21 points meeting every line in at most five points. Hence the least possible largest line intersection of an `H`-invariant blocking set is 5.

Every fixed-point-free collineation of order three of `PG(2,13)` generates a conjugate of `H`, so the statement holds for all of them; this step has a conventional proof. The proof reduces the question to 61 weighted line conditions on the `H`-orbits and shows by exhaustive search that no choice of orbits meets every line in one to four points. Blocking sets without this symmetry are not covered: whether `PG(2,13)` has a blocking set with all line intersections at most four is not decided here.

## Verification scope

- **Lean 4.35.0** ([lean/](lean/)): `PG(2,13)` is Mathlib's projectivization of `F₁₃³`, with lines given by dot products. The project proves that the Singer cycle has order 183 and that `H` has order three and no fixed point, the properties of the 21-point witness, the reduction of arbitrary `H`-invariant sets to the 61 conditions, the nonexistence of a solution, and the final statement `SingerC3.isLeast_admissibleCaps`. The search runs in the Lean kernel with `decide +kernel` as a top search and 342 subsearches, 771,752 steps in total; its soundness theorem holds for every value of the search heuristic. There is no `native_decide`, and every project declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. See [theorem-map.json](theorem-map.json).
- **Exact checks** ([certificate/check_singer.py](certificate/check_singer.py)): an independent standard-library program rebuilds the field, all points and lines from their coordinate equations, the 61 conditions and the witness, checks the witness's intersection numbers, tangents and conjugacy to the set of Blokhuis, Brouwer and Wilbrink, and repeats the exhaustive search (156,717 nodes).
- **Conventional:** the conjugacy of all fixed-point-free subgroups of order three (manuscript, Section 5).

## Prior work and priority

The matching 21-point example is due to Blokhuis, Brouwer and Wilbrink, *Blocking sets in PG(2,p) for small p, and partial spreads in PG(3,7)*, Adv. Geom. 3 (2003), S245–S253; no new construction is claimed. Erdős, Silverman and Stein (1983) proved the logarithmic bound for general planes. The searched literature and the campaign record did not settle this symmetric case; historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project; [Audit.lean](lean/Audit.lean) audits the axioms of every project declaration and prints those of the principal ones.
- [certificate/](certificate/) and [witnesses/](witnesses/): the exact checker and the 21-point witness.
- [Verification instructions](VERIFICATION.md), [verify.py](verify.py) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
