# Sharp root log-concavity of alternating Motzkin sums

This paper proves Conjecture 1 of Feng-Zhen Zhao and improves its starting index from nine to five. The root sequence is strictly log-concave on this tail. The reverse inequality at center five proves that no earlier tail is log-concave.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite this paper. The [Lean guide](../../lean/docs/alternating-motzkin.md) maps the claims to declarations. The [verification guide](../../verification/alternating-motzkin/README.md) gives commands and check limits.

The Motzkin recurrence and alternating sum are given in [Zhao, INTEGERS 26 (2026), A55, equations (1) and (2)](https://math.colgate.edu/~integers/aa55/aa55.pdf).

$$
M_0=M_1=1,\qquad (n+3)M_{n+1}=(2n+3)M_n+3nM_{n-1}\quad(n\ge1),
$$

$$
T_n=\sum_{j=0}^{n}(-1)^{n-j}M_j.
$$

Set $r_n=T_n^{1/n}$ for $n\ge2$. Then $T_n>0$, and

- $r_n r_{n+2}<r_{n+1}^{2}$ for every $n\ge5$;
- $r_5^2<r_4r_6$.

A tail starting at five has centers six and above. The failed inequality at center five therefore establishes the sharp threshold. The theorem also proves Zhao's claim for the tail starting at nine.

Lean specifies the recurrence over the rational numbers and takes real powers of the exact finite sums. It proves existence and uniqueness for the recurrence. It also proves that the finite sum equals the recursive sequence used in the analytic proof. This correspondence assumes only the recurrence and initial values. A lattice-path interpretation and the separate assertion that the roots increase to three are outside the formal claim.

The proof uses established methods. [Došlić and Veljan](https://doi.org/10.1016/j.disc.2007.04.066) develop interlacing methods and Motzkin ratio bounds. Zhao gives related bounds for the alternating sums. [Chen, Guo, and Wang](https://arxiv.org/abs/1304.5160) give a general root criterion. [Hou and Li](https://arxiv.org/abs/2310.19234) give methods for sequences that satisfy polynomial recurrences. The contribution here is the alternating-sum inequality with its sharp threshold.

The sequence is also listed as [OEIS A187306](https://oeis.org/A187306). No claim of first priority is made.

Dev D. Goyal directed the research and is responsible for publication. ChatGPT (OpenAI), using GPT-6 with Pro reasoning, generated the mathematical arguments and Lean formalizations. Codex assisted with formalization, computations, and editing. [AUTHORSHIP.md](../../AUTHORSHIP.md) gives the collection disclosure. This preprint has not been peer reviewed.