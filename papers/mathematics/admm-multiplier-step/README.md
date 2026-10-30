# A narrow interval for the universal multiplier step of two-block ADMM

**Fully autonomous agentic research.** Autonomous AI research agents produced the certificates, proofs, Lean formalization and earlier drafts; Opus 5.5 by Anthropic used with Claude Code consolidated, rechecked and rewrote this release. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

I study classical two-block ADMM with a fixed penalty when only the multiplier update is scaled by a constant step `tau`. In consensus form with penalty one, the iteration is

```text
x_next = argmin_{x in C} f(x) + ||x - z + u||^2 / 2
z_next = argmin_{z in D} g(z) + ||x_next - z + u||^2 / 2
u_next = u + tau * (x_next - z_next).
```

**Convergence.** For every fixed `0 < tau <= 943/500 = 1.886`, the iteration converges on every finite-dimensional real inner-product space. The hypotheses are convex functions on convex effective domains, attainment of both proximal minima for every center, and existence of a saddle. Both primal blocks converge to a common constrained minimizer, the multiplier converges to a saddle multiplier, and the objective values converge to the optimum. No smoothness, strong convexity, bounded iterates or summability is assumed. An affine-constraint version, `A(x) = B(y)` with any positive penalty, gives convergence of the constraint images, multiplier and objective values. With continuous left inverses for the affine maps, the raw primal iterates also converge.

**Obstruction.** One fixed pair of compact convex polytopes in `R^128`, with zero objectives on them, has a nonconstant periodic ADMM orbit for every `tau >= 897744153596994489/475778439151265168 ≈ 1.8868954`. The origin is a saddle, and the primal residual is constant and positive.

Consequently, the largest step with universal convergence lies in `[1.886, 1.8868954…]`, an interval of width less than `0.0009`. The exact threshold is open. The obstruction uses indicator objectives; smooth or strongly convex subclasses are not addressed. The same collection's earlier [five-cycle at `tau = 199/100`](../admm-counterexample/) is a separate, coarser obstruction.

Gao et al. (2022) asserted convergence of this iteration for every `1 < tau <= 2`. The manuscript explains why that assertion fails, and the polytope orbit contradicts it for every `tau >= 1.8868954…`.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean sources](lean/): 168 proof modules and the central kernel-recheck audit. The six central declarations are listed in [VERIFICATION.md](VERIFICATION.md).
- [Exact certificates](certificates/): two rational finite-memory interval certificates and the integer cyclic witness.
- [Exact checkers](checks/): standard-library Python programs that rebuild the certificate identities with rational arithmetic.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Discovery scripts](discovery/): the numerical searches and exact reconstructions used to find the certificates. They are not proof dependencies.
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
