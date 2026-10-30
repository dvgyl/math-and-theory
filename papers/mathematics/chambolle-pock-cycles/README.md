# Periodic obstructions to small-extrapolation Chambolle–Pock

**Fully autonomous agentic research.** Autonomous AI research agents produced the constructions, certificates and Lean proofs; Opus 5.5 by Anthropic used with Claude Code rechecked them and rewrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

The unmodified primal-first Chambolle–Pock (PDHG) iteration with extrapolation `θ` and step product `κ = τσ‖L‖²` converges for `θ > 1/2` and `κ < 4/(1+2θ)` (Banert, Upadhyaya and Giselsson), and for small `θ` under a sufficient condition of order `8θ` (Upadhyaya). This package proves necessary restrictions:

- **Every step product above two.** For every fixed `κ > 2`, fixed compact polytopes in `ℝ⁴`, with zero objectives, give a nonconstant periodic, nonconvergent orbit for every `0 ≤ θ ≤ ε`. Any universal sufficient condition `κ < c(θ)` therefore has `limsup_{θ↓0} c(θ) ≤ 2`, below the quadratic stability bound `4/(1+2θ)`.
- **The exact three-cycle threshold.** A nonconstant three-cycle of actual convex proximal updates exists exactly when `κ²(1+θ)² − 2κ(1+3θ) − 3 ≥ 0`; compact triangles attain the boundary.
- **A robust rational seven-cycle** on the parameter rectangle `2.499 ≤ κ ≤ 2.501`, `0 ≤ θ ≤ 1/400`, with an open set of nonconvergent initial states.

The obstructing extrapolation intervals are very small, the bound two is not shown to be sharp, and the full small-`θ` convergence region remains open. The manuscript states these limits.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex), with the [parameter figure](figures/).
- [Lean project](lean/): 21 modules and the strict verifier [`verify_lean.py`](lean/verify_lean.py). [FORMAL_CORRESPONDENCE.md](FORMAL_CORRESPONDENCE.md) maps the mathematical claims to Lean declarations.
- [Exact seven-cycle certificate](exact_certificate/) with a standard-library rational checker and the generator of `lean/SevenCycle.lean`.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
