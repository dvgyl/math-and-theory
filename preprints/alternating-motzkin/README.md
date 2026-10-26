# Sharp root log-concavity of alternating Motzkin sums

This paper proves Conjecture 1 of Feng-Zhen Zhao and improves its starting index from nine to five. The root sequence is strictly log-concave from index five. The reverse inequality at center five proves that no earlier tail is log-concave.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite this paper. The [Lean guide](../../lean/docs/alternating-motzkin.md) maps the claims to declarations. The [verification guide](../../verification/alternating-motzkin/README.md) gives commands and check limits.

The source is [Zhao, INTEGERS 26 (2026), A55](https://math.colgate.edu/~integers/aa55/aa55.pdf). Equations (1) and (2) specify

$$
M_0=M_1=1,\qquad (n+3)M_{n+1}=(2n+3)M_n+3nM_{n-1}\quad(n\ge1),
$$

$$
T_n=\sum_{j=0}^{n}(-1)^{n-j}M_j.
$$

Set $r_n=T_n^{1/n}$ for $n\ge2$. Then $T_n>0$, and

- $r_n r_{n+2}<r_{n+1}^{2}$ for every $n\ge5$;
- $r_5^2<r_4r_6$.

A tail starting at five has centers six and above. Thus the failed center-five inequality does not conflict with the first statement. The result includes the source's weaker claim of log-concavity on the tail starting at nine.

Lean specifies the source recurrence over the rational numbers and takes real powers of the exact finite sums. It proves existence and uniqueness for the recurrence. It also proves that the finite sum equals the recursive implementation used by the analytic proof. No bound or conclusion is assumed in this correspondence. The formal claim does not include a lattice-path interpretation or the separate assertion that the roots increase to three.

The proof uses established methods. [Došlić and Veljan](https://doi.org/10.1016/j.disc.2007.04.066) develop interlacing methods and Motzkin ratio bounds. Zhao supplies related bounds for the alternating sums. [Chen, Guo, and Wang](https://arxiv.org/abs/1304.5160) give a general root criterion. [Hou and Li](https://arxiv.org/abs/2310.19234) give methods for sequences that satisfy polynomial recurrences. These references support the method; they are not new results of this paper.

The prior-work search used the source conjecture, equivalent root inequalities, “alternating Motzkin”, and [OEIS A187306](https://oeis.org/A187306). The inspected sources did not identify an earlier proof of this exact result. This was a bounded search on 26 October 2026. Direct Google Scholar, zbMATH, and MathSciNet queries were inaccessible. Searches restricted to their public web indexes did not complete those database searches. The Hou–Li journal record was accessible, but its full journal text required a subscription; the arXiv manuscript was inspected. No claim of first priority follows from these searches. The [verification guide](../../verification/alternating-motzkin/README.md) records the public-formalization search limits.

Dev D. Goyal directed the research. AI systems produced the proofs and formalizations under his direction. See [AUTHORSHIP.md](../../AUTHORSHIP.md) for the disclosure. This paper has NOT been peer reviewed. Native Lean compilation, axiom checks, finite computations, statement comparison, and referee review are separate checks. Final Comparator, final referee, and fresh-clone verification are not claimed by this page.
