# The multi-marginal converse of Minty's theorem fails in the plane

**Fully autonomous agentic research.** Autonomous AI research agents produced the counterexample, the proof, the Lean formalization and an earlier version of the note; Opus 5.5 by Anthropic used with Claude Code checked the statement against the source question, rechecked the certificate with its own exact code, ran a fresh Lean replay and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Minty's theorem says that a monotone set `Γ ⊆ H × H` is maximally monotone exactly when `x₁ + x₂` ranges over all of `H` as `(x₁, x₂)` ranges over `Γ`. Bartz, Bauschke, Phan and Wang (*Multi-marginal maximal monotonicity and convex analysis*, Math. Program. 185, 2021) extended one direction to `N` marginals with the cost `c(x) = Σ_{i<j} ⟨xᵢ, xⱼ⟩` and asked in Remark 2.6 whether the other direction holds: does maximal `c`-monotonicity force the sum image `S(Γ) = {x₁ + ⋯ + x_N : x ∈ Γ}` to be all of `H`?

**Theorem.** For three marginals on `ℝ²` there is a three-point `c`-monotone set `Γ₀` such that no `c`-monotone superset contains a tuple with sum zero. Consequently every maximally `c`-monotone set containing `Γ₀`, and one exists by Zorn's lemma, has a sum image that omits `0` and is not convex. The answer to the question of Remark 2.6 is therefore negative.

The points of `Γ₀` have integer coordinates. Four of the compatibility inequalities that a zero-sum tuple would have to satisfy have a positive weighted sum equal to a sum of four squares plus `23/26`, which rules out every real zero-sum tuple. The sums of the three points have the positive convex combination `28 S(A) + 173 S(B) + 205 S(C) = 0`, which gives nonconvexity. Equivalently, a partition of the identity on three points into three firmly nonexpansive maps cannot be extended jointly to the origin.

## Prior work and priority

Lim (SIAM J. Optim. 33, 2023) showed that contact sets of multi-conjugate tuples need not be maximal in dimension two; his example has a sum image with a hexagonal hole, but it can be enlarged by the zero tuple, so it does not answer Remark 2.6. Searches in October 2026 found no earlier answer. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project. The endpoints are `Minty.exists_maximal_cMonotone_nonconvex_sum` and `Minty.not_all_maximal_cMonotone_have_full_sum` in [Counterexample.lean](lean/Minty/Counterexample.lean); [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps the manuscript to the declarations.
- [certificate/verify_minty_exact.py](certificate/verify_minty_exact.py): exact rational check of the table and the identity.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
