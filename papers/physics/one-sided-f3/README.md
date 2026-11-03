# Exact one-sided filtering of the two-qubit F₃ functional

**Fully autonomous agentic research.** Autonomous AI research agents found the formulas, their proofs, the exact and numerical checkers and the Lean development in an earlier session. Opus 5.5 by Anthropic used with Claude Code checked the source question and the central proofs, reran every checker, wrote an independent brute-force comparison, rebuilt the Lean project with a new whole-project axiom audit and edited the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Dev D. Goyal · 3 November 2026

## The question

Write a two-qubit state in Bloch form with local vectors `a`, `b` and Pauli correlation matrix `T`, and let `F₃(ρ) = ‖T‖_F`. This is the optimized value of the three-setting linear steering inequality in the form used by Costa and Angelo, and `F₃ > 1` certifies steering. Ducuara, Susa and Skrzypczyk, *Locally inaccessible hidden quantum correlations* ([arXiv:2406.03945](https://arxiv.org/abs/2406.03945), [Phys. Rev. A 110, 022435 (2024)](https://doi.org/10.1103/PhysRevA.110.022435)), define one-sided hidden measures, in which only Alice or only Bob applies an invertible local filter `K`. For F₃ these are

```
H_F3A(ρ) = max over K ∈ GL(2,C) of F₃((K⊗I) ρ (K⊗I)† / tr(...))     (their Eq. 10, W = A)
H_F3B(ρ) = the same with I⊗K                                        (their Eq. 10, W = B)
```

Equation 9 defines the corresponding CHSH measures. The two-sided measures have closed expressions through the Bell-diagonal normal form (their Eqs. 7 and 8). The authors write that "there are currently no closed formulas for the one-sided versions defined in (9) and (10)" and list deriving such formulas among their open questions. Equation numbers refer to arXiv version 1.

## The answer

This package gives closed formulas for **both quantities of Equation 10**, H_F3A and H_F3B, for every two-qubit density matrix. It does **not** treat the one-sided CHSH measures of Equation 9, which remain open. Because Equation 10 quantifies invertible filters, its "max" is in general a supremum, and the package decides exactly when it is attained.

For Alice's filter and a mixed Alice marginal (`‖a‖ < 1`), put

```
δ = 1 − ‖a‖²,   B = T − a bᵀ,   c = (b − Tᵀa)/δ,   Q = Bᵀ(δI + a aᵀ)B/δ²,
β = ‖c‖²,   τ = tr Q,   d = τ − β,   M = [[Q, I], [Q c cᵀ, Q]]  (6×6).
```

Here `(c, Q)` are the centre and shape matrix of Bob's steering ellipsoid. Let `ν` be the largest real eigenvalue of `M` and `η = max(d, ν)`. Then

```
H_F3A(ρ)² = β + η + cᵀ Q (ηI − Q)⁺ c,
```

where `⁺` is the Moore–Penrose inverse, so all singular cases are included. If `‖a‖ = 1` the state is a product and `H_F3A = ‖b‖`. Bob's value is the same rule after `(a, b, T) ↦ (b, a, Tᵀ)`. An equivalent form uses only six scalar invariants of `(Q, c)` and the largest real root of an explicit sextic.

The manuscript also proves:

- **Optimality and filters.** An explicit S-lemma gap identity certifies the value. Every optimal filter is described, and, for a mixed filtered marginal, an invertible optimal filter exists exactly when the multiplier `η − d` is zero and the minimum-norm stationary point lies inside the unit ball.
- **The violating branch is rational.** `H_F3A > 1` exactly when `dI − Q ≻ 0`, `cᵀQ(dI − Q)⁻²c < 1` and `τ + cᵀQ(dI − Q)⁻¹c > 1`. Then `H_F3A² = τ + cᵀQ(dI − Q)⁻¹c`, and the optimal effect is unique up to scale.
- **No formula in radicals.** A strictly positive rational state, with `a = 0`, `c = (1/5, 1/6, 1/7)` and canonical correlation matrix `diag(1/20, 1/15, 1/10)`, has an optimal squared value of degree six whose Galois group is `S₆`.
- **Examples.** For the amplitude-damping Choi state with unfiltered `F₃² = 24/25`, `H_F3A² = 12/11` and `H_F3B² = 120/71`. Pure entangled states give `√3` on both sides.
- **Extensions.** The exact frontier at a prescribed success probability (at most fourteen algebraic candidates), the highest success rate compatible with the optimum, continuity properties, a sharp bound `H_F3A ≤ √(1 + (1+3r)²/(3+6r−r²))` from one rank-one conditional state of Bloch length `r`, and the set of limit values at every pure-marginal state.

## What is checked, and how

- **Lean** ([lean/](lean/)): `FilteredF3.equation10_both_closed_forms` proves, for every `M : Milne.CMatrix` with `Milne.Density M` (a positive semidefinite complex 4×4 matrix of trace one, with no rank assumption), that the square root of the explicit algebraic value is the least upper bound of `‖T‖_F` over all success-normalized states `(K⊗I)M(K⊗I)†/p` with `det K ≠ 0`, and likewise for `I⊗K`. The right side is the pure-marginal value or the spectral value of the whitened state. It is built from mathlib's eigenbasis and the greatest real root of an explicit polynomial, whose existence is proved, and it contains no optimization over filters. The formalization also covers the gap identity, all maximizers, attainment by invertible filters, the companion-determinant identity and the rational violating criterion in canonical coordinates. A whole-project audit checks every declaration of the 41 modules that define declarations.
- **Not formalized:** the rational Bloch-coordinate formulas for `(c, Q)` (Lean uses the equivalent whitened-state form), the six-invariant rule, the separability corollary, the Galois argument, and all extensions apart from some scalar lemmas. The Lean functional is the Frobenius expression of Eq. 3; its derivation from measurement optimization is cited. These parts are written proofs with exact certificates and floating-point checks.
- **Checks** ([checks/](checks/)): `python3 checks/run_checks.py --independent` replays a standard-library Galois certificate, two exact SymPy evaluators (23 exact rational cases, including every pole order, plus companion-polynomial identities), two separate Float64 implementations (800 and 514 one-sided instances), the extension and conditional-state checks, and a brute-force comparison written for this release. The comparison maximizes over all complex 2×2 filters directly on 4×4 matrices for 24 states of ranks 1 to 4. Floating-point checks detect errors; they are not proofs.

## Prior work and priority

The question and the measures are due to Ducuara, Susa and Skrzypczyk. The three-setting steering inequality is from Cavalcanti, Jones, Wiseman and Reid (2009), in the form of Costa and Angelo (2016). Steering ellipsoids and canonical filtering are due to Jevtic, Pusey, Jennings and Rudolph (2014) and Milne et al. (2014). The spectral trust-region method is classical: Gander, Golub and von Matt (1989), and Adachi, Iwata, Nakatsukasa and Takeda (2017). The new parts are the reduction of actual one-sided filtering to it and the consequences above. A literature search in November 2026 found no earlier closed formula for these measures. This does not establish priority.

**Earlier public work on related statements.** The Lean library in [lean/QuantumPrior](lean/QuantumPrior/) is adapted, with attribution, from my earlier steering-ellipsoid formalization, from which [steering-bounds](../steering-bounds/) was released. It includes the fully-entangled-fraction bound f(ρ) ≤ 1 − c/2, which is Conjecture 2 of Milne, Jennings, Jevtic and Rudolph ([arXiv:1404.3951](https://arxiv.org/abs/1404.3951)). The Omega Institute's public repository [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing) records a claimed Lean proof of that conjecture, committed on 8 October 2026 (issue #14206). It also records a proof of their Conjecture 1, on the CHSH value at fixed centre, committed on 14 October 2026 (issue #16558). I make no priority claim for either statement. Neither is used by the main theorem here, and neither record contains the one-sided filtered measures. This package contains no code from the Omega repository. The [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#omega-steering-centre-bounds) gives the sources.

## Files

- [Manuscript](manuscript.pdf), its [LaTeX source](manuscript.tex), [sections/](sections/) and [figures/](figures/).
- [lean/](lean/): the Lean project. [AxiomAudit.lean](lean/AxiomAudit.lean) audits it, and [QuantumPrior/README.md](lean/QuantumPrior/README.md) records the provenance of the reused library.
- [checks/](checks/): checkers, exact evaluators and their recorded JSON reports.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
