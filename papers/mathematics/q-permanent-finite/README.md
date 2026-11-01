# Finite real counterexamples and spectral obstructions for q-permanent monotonicity

**Fully autonomous agentic research.** Autonomous AI research agents found the finite witness, its certificate, the proofs and an original Lean development in earlier sessions; Opus 5.5 by Anthropic used with Claude Code rechecked the certificate with its own independent exact program, checked the central proofs, removed native evaluation from the Lean development, ran a fresh Lean replay and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

For an ordered `n × n` matrix `A`, the inversion-weighted q-permanent is

```
P_q(A) = Σ_{σ ∈ S_n} q^{inv(σ)} Π_i a_{i,σ(i)},   inv(σ) = #{i < j : σ(i) > σ(j)},
```

and `D_q(A)` is its derivative in `q`. The row order is part of the data. At `q = −1, 0, 1` it gives the determinant, the diagonal product and the permanent.

**Theorem 1 (finite real endpoint counterexample).** The 224 integer types in [certificate/witness896_cap32_orbits.txt](certificate/witness896_cap32_orbits.txt), read by the four-row rule of the manuscript, give 896 ordered rows `v_i ∈ ℤ³` with coordinates of absolute value at most 32. Their Gram matrix `B = (v_i · v_j)` is positive semidefinite of rank exactly three, and

```
1000 U > 1001 · C(896,2) · per(B),   hence   D₁(B)/per(B) < −5012/25,
```

where `U` is an explicit lower bound for the squared Fischer norm `T` of the ordered wedge polynomial and `2D₁(B) = C(896,2) per(B) − T`. The permanent has 4152 decimal digits; the exact value is `D₁(B)/per(B) ≈ −385.94`.

**Theorem 2 (explicit positive-definite matrix and rational pair).** With `M = 10⁴·896³`, `H = 2490M + 1` and `Q = 4·896!·896⁴·H^896`, the integer matrix `A = MB + I` is positive definite with least eigenvalue 1, and `q₁ = 1 − 2/Q`, `q₂ = 1 − 1/Q` satisfy `0 < q₁ < q₂ < 1` and `P_{q₂}(A) < P_{q₁}(A)`; since `Q` has 16834 digits, the pair lies extremely close to 1. Since `P_q(A ⊕ I_k) = P_q(A)`, real positive-definite counterexamples exist in every order `N ≥ 896`, with one rational pair for all of them.

The manuscript also proves fixed-rank asymptotic results for `I_N + (t/N)V_N V_Nᵀ` with bounded rows: correlation counterexamples with off-diagonal entries `O(1/N)` and condition number tending to 227; positivity of the endpoint derivative for every ordering when `tλ_max(Σ) < 1`, and, with an explicit margin, whenever `tλ₃(Σ) ≤ 1 < tλ₁(Σ)`; exponential rarity of negative orders under random ordering; and a one-parameter reduction of the coherent ordering problem.

## The conjecture and its status

Bapat and Lal (*Inequalities for the q-permanent*, Linear Algebra Appl. 197–198 (1994)) asked whether `P_q(A)` is strictly increasing on `[−1, 1]` for every non-diagonal positive-definite Hermitian matrix; Mitchell (Oper. Matrices 14 (2020)) showed the equivalence with the positive-semidefinite form with positive diagonal. Da Fonseca conjectured strict monotonicity for real symmetric positive-definite matrices on an interval reaching `+∞` with left endpoint at or below `−1` ([Linear Algebra Appl. 432 (2010), Conjecture 1](https://doi.org/10.1016/j.laa.2009.10.036)), restated with left endpoint below `−1` in [arXiv:1804.02231, Conjecture 2](https://arxiv.org/abs/1804.02231). Kenta Kitamura's [Lean formalization](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b) disproved the Hermitian conjecture with a complex matrix of order 144. The [public problem record MI-18](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-18/README.md), consulted on 1 November 2026, lists the real-symmetric case as unsettled. The companion package [q-permanent](../q-permanent/README.md) refuted da Fonseca's conjectures for `q > 1` and left the real-symmetric question on `[−1, 1]` open.

Theorems 1 and 2 answer that real-symmetric question negatively: a real symmetric positive-definite matrix can have a strictly decreasing q-permanent inside `(0, 1)`. They also refute da Fonseca's conjectures inside the original interval. The minimum order, minimum rank, the negative half-interval and failure at a prescribed interior parameter remain open. The repository's [correspondence record](../../../CORRESPONDENCE.md) summarizes an exchange with Carlos M. da Fonseca about the companion package; it predates this package and implies no endorsement of it.

## What is verified, and how

| Part | Status |
|---|---|
| Definition of `P_q` and `D_q`; the identity `2D₁(VVᵀ) = C(n,2)‖f‖² − ‖G‖²` for real `n × 3` matrices; the four-row recurrence, parity decomposition and integer evaluator; certificate soundness for every type list; reduction of a negative endpoint to a rational positive-definite matrix with rational `0 < q₁ < q₂ < 1`; identity padding; rank three of the frozen witness; the all-orders statement from the certificate hypothesis | **Formal.** Lean 4.19.0 with Mathlib `c44e0c8`, 32 modules. A whole-project audit covers every declaration; all 749 declarations other than Lean 4.19 code-generation auxiliaries depend only on `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no added axiom, no `native_decide`, no `Lean.ofReduceBool`. |
| The finite comparison `1001·C(896,2)·per(B) < 1000U ≤ 1000T` for the frozen witness | **Exact certificate, outside Lean.** The integer program [exact_orbits.cpp](certificate/exact_orbits.cpp) evaluates the four-row recurrence with GMP. The independent program [row_residues.cpp](certificate/row_residues.cpp) uses neither the symmetry nor the recurrence: it expands the ordinary row-by-row product and wedge recurrences modulo 500 primes, and the Chinese remainder theorem then determines `per(B)`, `U` and `T` exactly. Both agree with the frozen integers. [verify_certificate.py](certificate/verify_certificate.py) checks everything with the Python standard library. |
| Explicit `A = MB + I`, `Q`, `q₁`, `q₂`; the asymptotic, spectral, random-order and coherent-ordering theorems | **Conventional proofs** in the manuscript. The regularization was checked line by line for this release; the asymptotic sections were read but not rederived line by line. Their scalar constants and two finite matrix steps are formalized. |

An earlier stage evaluated the certificate inside Lean with `native_decide`, which adds `Lean.ofReduceBool` and the compiler to the trusted base; that module is not included. The certificate is therefore not a closed Lean theorem: Lean proves that the stated finite inequality implies the counterexamples, and the exact programs check the inequality.

## Prior work and priority

The ordered-wedge form of the endpoint identity follows Kitamura's formalization, and parts of the Lean proof adapt his Apache-2.0 sources. Mitchell also proved the rank-one and order-three cases. A public manuscript by liqsweep claims permanent-on-top for real positive-semidefinite matrices of rank at most two, which has a qualitative rank-two endpoint consequence; no priority is claimed for that consequence. Literature searches through 1 November 2026 found no real-symmetric counterexample on `[−1, 1]`. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf), its [LaTeX source](manuscript.tex), the section files in [sections/](sections/) and the [bibliography](references.bib).
- [certificate/](certificate/): the frozen inputs (order 896, primary; order 1024 with the larger margin `250U > 251·C(1024,2)·per(B)`), the exact reports, the residue record, the regularization parameters and the exact programs.
- [lean/](lean/): the Lean project. The frozen-input statements are in [Witness896.lean](lean/QPermanentResearch/Witness896.lean); [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps the manuscript to the declarations; [THIRD_PARTY_NOTICES.md](lean/THIRD_PARTY_NOTICES.md) and [LICENSE-Kitamura](lean/LICENSE-Kitamura) cover the adapted sources.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
