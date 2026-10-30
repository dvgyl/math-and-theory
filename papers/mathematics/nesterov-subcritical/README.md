# Escaping Nesterov flows and iterates below critical damping

**Fully autonomous agentic research.** Autonomous AI research agents produced the three underlying packages; Opus 5.5 by Anthropic used with Claude Code extended the planar result, merged and rechecked the Lean proofs, and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

I study zero-velocity solutions of the Nesterov differential equation

```math
X''(t)+\frac{r}{t}X'(t)+\nabla F(X(t))=0,\qquad X'(0)=0,
```

and the Nesterov iteration `X_{k+1} = Y_k - ∇F(Y_k)`, `Y_{k+1} = X_{k+1} + k/(k+r) (X_{k+1} - X_k)`, for convex `F` with a globally 1-Lipschitz gradient and an attained minimum. For `r ≥ 3` every trajectory and every sequence of iterates is bounded. The results show that this threshold is sharp:

- **Hilbert space, continuous time.** On `ℓ²(ℕ; ℝ²)`, universal boundedness of zero-velocity solutions holds exactly when `r ≥ 3`. For each `0 < r < 3`, an explicit block sum of smoothed valleys has a trajectory whose norm tends to infinity.
- **Hilbert space, discrete time.** The same holds for the unit-step iteration with momentum `k/(k+r)`, the Chambolle–Dossal family.
- **An explicit planar valley.** For `f(x,y) = h(√(x²+y²)) − x`, with the Huber function `h`, the solution from `(2,1)` at rest escapes to infinity for every `0 < r ≤ 2` and stays bounded for every `r > 2`.

Whether a finite-dimensional objective has an unbounded zero-velocity trajectory for some `2 < r < 3` remains open. The minimizer sets in all examples are unbounded, which is necessary in finite dimension.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): the unchanged modules of the three uploaded developments and the new planar modules (`Planar*`, `EulerObstruction`), with [`Audit.lean`](lean/Audit.lean) and the strict verifier [`verify_release.py`](lean/verify_release.py).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
