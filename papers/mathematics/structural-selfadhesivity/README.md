# Structural selfadhesivity does not imply a numerically selfadhesive realization

**Fully autonomous agentic research.** Autonomous AI research agents produced the construction, the exact certificates, the Lean formalization and an earlier version of the note; Opus 5.5 by Anthropic used with Claude Code checked the statement against the source question, reran the exact checkers and a fresh Lean replay, and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

**Theorem.** There is an explicit conditional-independence model `M` on five variables, with 26 of the 80 elementary CI statements, such that

- for every overlap `L ⊆ {1,…,5}` there is a real polymatroid on the glued ground set that is adhesive at `L` and whose two restrictions both induce exactly `M` (structural selfadhesivity), but
- no real polymatroid `h` that induces exactly `M` is selfadhesive in Matúš's numerical sense, that is, admits for every `L` an adhesive extension whose two restrictions both equal `h`.

This answers negatively Question 4.18 (4.14 in the PDF version) of T. Boege, *Selfadhesivity in Gaussian conditional independence structures* (IJAR 2023, arXiv:2205.07667), which asked whether every structurally selfadhesive structural semigraphoid is induced by a selfadhesive polymatroid; Boege's computation gave a positive answer for four variables. The positive part is certified by 32 explicit integer polymatroids; the negative part by an exact identity among 51 nonnegative conditional mutual informations and two adhesive gaps, valid for every real inducing profile.

## Prior work and priority

The notions are due to Matúš and to Boege, Bolt and Studený, who proved that numerical selfadhesivity implies structural selfadhesivity. A five-variable counterexample to a neighbouring question (Open Problem 3 of Boege–Bolt–Studený) was posted in August 2026 in the ScaleMath repository, another AI research project; its model fails a structural gluing, whereas `M` passes all of them, and the higher-dimensional-face and exact-identity methods are credited to it. Studený's earlier inequalities already show that `M` is not entropic; that is not claimed here. Searches in October 2026 found no earlier answer to Boege's question. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex), with all witness tables and the separating identity.
- [proof/e3_lean/](proof/e3_lean/): the Lean project; the main statements are `InfoE3.counterexample` and `InfoE3.counterexample_all_labelings` in [Main.lean](proof/e3_lean/InfoE3/Main.lean), with definitions in [Defs.lean](proof/e3_lean/InfoE3/Defs.lean).
- [proof/](proof/): the verification driver, the certificates and exact standard-library checkers, and the generators of the witness and certificate modules.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
