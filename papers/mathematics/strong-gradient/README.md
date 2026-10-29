# The exact last-gradient bound for constant-step gradient descent in the strongly convex case

**Fully autonomous agentic research.** Automated systems produced the research, proofs, formalization, and manuscript preparation. I am responsible for publication. No expert validation or peer review is claimed.

I present the exact final-gradient guarantee for constant-step gradient descent on a differentiable function with an L-Lipschitz gradient and strong-convexity parameter μ, on any real Hilbert space. The initial error is distance to an actual global minimizer. For L > 0, 0 ≤ μ ≤ L, normalized step 0 ≤ h ≤ 2, and every natural horizon N,

```math
\|\nabla f(x_N)\| \le L\|x_0-x_*\|\max\{p_N(\mu/L,h),\ |1-h|^N\},
\qquad x_{i+1}=x_i-\frac hL\nabla f(x_i),
```

where

```math
p_N(\kappa,h)=
\begin{cases}
(1+Nh)^{-1},&\kappa=0,\\
\dfrac{\kappa(1-\kappa h)^N}{1-(1-\kappa)(1-\kappa h)^N},&0<\kappa\le1.
\end{cases}
```

The positive-curvature denominator is positive. The formula includes zero bases and every closed boundary, with every zeroth power equal to one. Actual one-dimensional Huber and quadratic functions attain the two branches. The upper bound has no finite-horizon or dimension cutoff.

The intended contribution is the complete positive strong-convexity case of Taylor–Hendrickx–Glineur Conjecture 3. I credit the formula and sharp examples to Taylor, Hendrickx, and Glineur, the complete zero-curvature curve to Jones, and the factorized-certificate antecedents to Chikhi and Jones. The cited literature comparison does not establish worldwide priority.

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Proof map](PROOF_MAP.md): claims, exact hypotheses, endpoints, and formal declarations.
- [Verification instructions](VERIFICATION.md) and [Lean sources](lean).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), and [BibTeX](CITATION.bib).
- [Apache-2.0 license](LICENSE) and [retained MIT notice](lean/THIRD_PARTY_LICENSE).

The actual-function upper bound and normalized actual-function attainment are checked in Lean 4.19.0. Sharpness at arbitrary L and positive radius R is proved by rescaling in the manuscript; it is not a separate Lean wrapper.

I build the manuscript with two runs of `pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error manuscript.tex`.
