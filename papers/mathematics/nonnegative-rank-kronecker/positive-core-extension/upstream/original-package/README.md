# Counterexamples to the Kronecker-square lower bound for nonnegative rank

**Fully autonomous agentic research.** Autonomous AI research agents produced the construction, the proof, the Lean formalization, the exact certificate and an earlier version of the note; Opus 5.5 by Anthropic used with Claude Code checked the argument and the formal statement, ran a fresh Lean replay and an independent exact check, and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Vandaele, Gillis, Glineur and Tuyttens conjectured (*Heuristics for exact nonnegative matrix factorization*, J. Global Optim. 65, 2016, Conjecture 1 in §6.1) that every entrywise nonnegative matrix `M` satisfies

```math
\operatorname{rank}_+(M\otimes M)\ \ge\ \operatorname{rank}_+(M)\,\operatorname{rank}(M).
```

**Theorem.** Let `A` be the 4 × 4 circulant matrix with first row `(17, 17, 1, 1)`, and for `t ≥ 1` let `C_t = A ⊕ (J_{t+1} + ε_t I_{t+1})` with `ε_t = 1/(100800 t(3t+1))`. Then `C_t` is rational and nonnegative, `rank C_t = t + 4`, `rank₊ C_t = t + 5` and `rank₊(C_t ⊗ C_t) ≤ (t + 4)² + 9`, which is `t − 5` below the conjectured bound `(t + 5)(t + 4)`.

The smallest member `C_6` has order 11, rank 10 and nonnegative rank 11, and its 121 × 121 square has an explicit nonnegative rational factorization of width 109, against the conjectured bound 110. The saving comes from the mixed blocks `A ⊗ B_t`: a positive rank-one term absorbs a small real perturbation of rank `q` with only `q + 1` nonnegative terms, so these blocks have nonnegative rank at most `3t + 4` instead of `4(t + 1)`. The exact value of `rank₊(C_t ⊗ C_t)` is not determined.

## Prior work and priority

The seed `A` and its rank gap are classical (Vandaele et al.; Bocci, Carlini and Rapallo), and direct-sum additivity of nonnegative rank is known (Qi, Comon and Lim). Chauhan and Choudhury (arXiv:2607.27037, July 2026) proved the conjecture for matrices with at most three rows or columns and treat it as open in general. Searches in October 2026 found no earlier counterexample. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project. The endpoints are `MatCKronecker.exists_rational_counterexample_with_gap`, `counterexample_eleven` and `vandaele_gillis_glineur_tuyttens_conjecture_false` in [Counterexample.lean](lean/MatCKronecker/Counterexample.lean); [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps the manuscript to the declarations.
- [certificate/](certificate/): the exact order-11 factorization [C11_NMF109.json](certificate/C11_NMF109.json), its generator and verifier [exact_certificate.py](certificate/exact_certificate.py), and the independent check [check_factorization.py](certificate/check_factorization.py).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
