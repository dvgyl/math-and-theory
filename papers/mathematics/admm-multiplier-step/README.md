# A narrow interval for the universal multiplier step of two-block ADMM

**Fully autonomous agentic research.** Autonomous AI research agents produced the certificates, proofs, Lean formalization and earlier drafts; Opus 5.5 by Anthropic used with Claude Code consolidated, rechecked and rewrote this release and extended the Lean formalization to version 1.1. This is version 1.1 of 31 October 2026. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

I study classical two-block ADMM with a fixed penalty when only the multiplier update is scaled by a constant step `tau`. In consensus form with penalty one, the iteration is

```text
x_next = argmin_{x in C} f(x) + ||x - z + u||^2 / 2
z_next = argmin_{z in D} g(z) + ||x_next - z + u||^2 / 2
u_next = u + tau * (x_next - z_next).
```

**Convergence.** For every fixed `0 < tau <= 377359/200000 = 1.886795`, the iteration converges on every finite-dimensional real inner-product space. The hypotheses are convex functions on convex effective domains, attainment of both proximal minima for every center, and existence of a saddle. Both primal blocks converge to a common constrained minimizer, the multiplier converges to a saddle multiplier, and the objective values converge to the optimum. No smoothness, strong convexity, bounded iterates or summability is assumed. An affine-constraint version, `A(x) = B(y)` with any positive penalty, gives convergence of the constraint images, multiplier and objective values. With continuous left inverses for the affine maps, the raw primal iterates also converge.

**Obstruction.** One fixed pair of compact convex polytopes in `R^128`, with zero objectives on them, has a nonconstant periodic ADMM orbit for every `tau >= 38847831300265103262189027/20588352022933119368900773 ≈ 1.8868840`. The origin is a saddle, and the primal residual is constant and positive.

Consequently, the largest step with universal convergence lies in `[1.886795, 1.8868840…]`, an interval of width less than `0.00009`. The exact threshold is open.

**Scalar problems.** In dimension one the iteration converges, with the same conclusions, for every `0 < tau < 2`, and the trivial instance `C = D = R`, `f = g = 0` fails for every `tau >= 2`. The universal range for scalar problems is therefore exactly `(0, 2)`; the threshold depends on the dimension.

**Version 1.1.** Version 1.0 (30 October 2026) had the bracket `[943/500, 1.8868954…]`. Version 1.1 adds five exact interval certificates covering `[943/500, 377359/200000]`, a new integer orbit with a lower threshold and the scalar theorem, narrowing the bracket about tenfold. The statements of version 1.0 remain valid. The Lean formalization now covers the whole convergence range `0 < tau <= 377359/200000` with all seven interval certificates and the new orbit; the scalar theorem has a conventional proof (see [VERIFICATION.md](VERIFICATION.md)). The obstruction uses indicator objectives; smooth or strongly convex subclasses are not addressed. The same collection's earlier [five-cycle at `tau = 199/100`](../admm-counterexample/) is a separate, coarser obstruction.

Gao et al. (2022) asserted convergence of this iteration for every `1 < tau <= 2`. The manuscript explains why that assertion fails, and the polytope orbit contradicts it for every `tau >= 1.8868840…`.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean sources](lean/): 301 proof modules and the central kernel-recheck audit. The eleven central declarations and the exact formal scope are listed in [VERIFICATION.md](VERIFICATION.md).
- [Exact certificates](certificates/): seven rational finite-memory interval certificates covering `[7/4, 377359/200000]` and two integer cyclic witnesses (the current one and that of version 1.0).
- [Exact checkers](checks/): standard-library Python programs that rebuild the certificate identities with rational arithmetic.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Discovery scripts](discovery/): the numerical searches and exact reconstructions used to find the version 1.0 certificates. They are not proof dependencies. The searches behind the version 1.1 certificates are not included.
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
