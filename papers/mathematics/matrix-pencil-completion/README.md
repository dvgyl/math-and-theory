# Matrix-pencil rank distance as an explicit completion problem

**Fully autonomous agentic research.** Autonomous AI research agents produced the theorem, the proof, the Lean formalization and an earlier version of the note; Opus 5.5 by Anthropic used with Claude Code rechecked the formal statement, ran a fresh Lean replay and rewrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Let `F` be an infinite field and `A(t) = A₀ + tA₁`, `B(t) = B₀ + tB₁` be `m × n` pencils over `F`. Let `δ(A, B)` be the least rank over `F(t)` of `A′ − B′` over all pencils `A′`, `B′` strictly equivalent to `A`, `B` by constant invertible matrices. For `c, d ∈ F` put

```math
K_{c,d}(A)(t)=\begin{pmatrix}A(t)&0&I_m\\ 0&0&-(t-c)I_m\\ I_n&-(t-d)I_n&0\end{pmatrix}
```

**Theorem.** For distinct `c, d` and every integer `x ≥ 0`, `δ(A, B) ≤ x` if and only if `K_{c,d}(A) = P (K_{c,d}(B) ⊕ (t − d) I_x) Q` for one constant matrix `P` of full row rank and one constant matrix `Q` of full column rank, for both coefficients at once.

No regularity, rank or spectral hypothesis is imposed; the anchors may be eigenvalues and all dimensions may be zero. Over an algebraically closed field and at anchors outside the spectra, the strong block minimal bases theory of Dopico, Lawrence, Pérez and Van Dooren identifies `K_{c,d}(A)` with the barred pencil of Dodig and Stošić plus scalar blocks, and common-summand cancellation then gives Conjecture 1 of Dodig and Stošić, *Is the bounded rank perturbations problem for matrix pencils just a completion problem?* (ELA 41, 2025): the bounded rank perturbation problem for matrix pencils is a completion problem. That identification is cited and not formalized.

## Prior work and priority

The dilation is block minimal bases machinery, and the complementary construction is Verdier's observation/control reduction of matrix pencils; these are credited in the manuscript. Dodig and Stošić proved the conjecture for rank bound one, for full-row-rank pencils and when the bound equals the rank distance. Three directly relevant articles (Dodig–Stošić, LAA 721, 2025; Dodig, LAA 737, 2026; Szántó, JPAA 222, 2018) could not be read in full during the literature comparison. Searches in October 2026 found no general proof of the conjecture. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean_p1/](lean_p1/): common-summand cancellation for rectangular matrix families over an infinite field (`MatCP1.matrix_common_summand_cancellation`).
- [lean_p1_converse/](lean_p1_converse/): the theorem, with the endpoint `MatCP1Converse.dilation_rank_distance_iff` in [DilationTheorem.lean](lean_p1_converse/MatCP1Converse/DilationTheorem.lean) and the [correspondence notes](lean_p1_converse/DILATION_CORRESPONDENCE.md).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
