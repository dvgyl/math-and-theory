# Optimal entanglement witnesses under ellipsoid containment: the Milne–Jennings–Rudolph conjecture and its chirality correction

**Fully autonomous agentic research.** Autonomous AI research agents produced the proofs, the Lean development, the exact and numerical checks and the draft report in an earlier session; Opus 5.5 by Anthropic used with Claude Code checked the conjecture statement against the source, read the central proofs, reran the checks, replayed the Lean development with a whole-project axiom audit and revised the text into the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

## The conjecture

Antony Milne, David Jennings and Terry Rudolph, *Geometric representation of two-qubit entanglement witnesses*, [Phys. Rev. A 92, 012311 (2015)](https://doi.org/10.1103/PhysRevA.92.012311), [arXiv:1407.8440](https://arxiv.org/abs/1407.8440), represent a unit-trace two-qubit entanglement witness `W` by an ellipsoid `E(W)` in the Bloch ball, with a chirality sign. Section IV D states, verbatim (arXiv v1 and v2):

> **Conjecture.** Let E\* be an ellipsoid lying inside the Bloch sphere and S be a set of two-qubit entanglement witnesses defined as follows: W ∈ S if and only if E representing W lies inside E\*. The optimal W ∈ S are then represented by E = E\*.

The authors add that it applies to any E\* in Class C or Class D. "Optimal in S" means that no member of S detects a strictly larger set of states.

## Results

Let `E*` be an ellipsoid in the Bloch ball that represents at least one witness, and let `S*` be the set of trace-one witnesses `W` with `E(W) ⊆ E*`.

**Theorem (necessity: the conjecture as stated holds).** Every witness optimal in `S*` has `E(W) = E*`. Every member of `S*` has a finer or equal member of `S*` whose ellipsoid is `E*`.

**Theorem (the converse fails).** For `0 ≤ p ≤ 1` let `W_p = ½[[p,0,0,0],[0,1−p,1,0],[0,1,1−p,0],[0,0,0,p]]`, the family of Example 2 of the same paper. Then

```
W_p = (p/(1−p)) W_{1−p} + ((1−2p)/(1−p)) P_+,    P_+ = |ψ⁺⟩⟨ψ⁺|,  |ψ⁺⟩ = (|01⟩+|10⟩)/√2,
```

so for every `0 < p < 1/2` the left-handed witness `W_p` and the right-handed witness `W_{1−p}` have the same full-dimensional Class D ellipsoid (semiaxes `1, 1, 1−2p`), and `W_{1−p}` detects strictly more states. Thus `W_p` represents `E* = E(W_p)` but is not optimal in `S*`. For `p = 1/4` the state `¾|ψ⁻⟩⟨ψ⁻| + ¼|ψ⁺⟩⟨ψ⁺|` gives `tr(ρW_{1/4}) = 1/8` and `tr(ρW_{3/4}) = −1/8`.

**Theorem (corrected characterization).** If `E*` is full-dimensional, `W` is optimal in `S*` if and only if `E(W) = E*` and `W` is right-handed. If `E*` is planar, `W` is optimal in `S*` if and only if `E(W) = E*`. Segments and points represent no witness.

So the printed conjecture (the necessity reading) is true, and the stronger "exactly those" reading is true in Class C and for planar targets but false for every full-dimensional Class D target, whose left-handed representatives are always strictly improvable. The classification rests on two published theorems, two-qubit decomposability (Woronowicz) and the complete Lorentz normal forms (Avron–Kenneth). The manuscript also gives an exact 4×4 semidefinite containment test that covers singular targets, a polynomial optimality test, a convex program with a unique rank-one optimizer, the exact detection and geometric orders of the family `W_p`, a sharp comparison interval for diagonal Class D mirrors, an open set of counterexamples, and Class C examples showing that fineness controls neither containment nor volume of ellipsoids.

## What is verified, and how

| Part | Status |
|---|---|
| The counterexample: `W_{1/4}`, `W_{3/4}` and, for every `0 < p < 1/2`, `W_p`, `W_{1−p}` are Class D witnesses (both they and their partial transposes are witnesses) with equal canonical ellipsoids, `W_{1−p}` is strictly finer, and `W_p` is not optimal in any set of matrices containing `W_{1−p}`; the exact fineness and geometric orders of the family; a same-chirality improvement with a properly smaller ellipsoid; a noncanonical Class C comparison with incomparable ellipsoids; normal-form positive-remainder certificates; the sharp mirror interval; soundness of the containment LMI and exact diagonal containment; product vectors in every two-dimensional subspace of C²⊗C² | **Formal.** Lean 4.19.0 with Mathlib `c44e0c8`, nine modules, for genuine complex 4×4 matrices; states range over all complex density matrices and block positivity over all complex product vectors. A whole-project audit covers every declaration of the nine modules; all declarations other than Lean 4.19 code-generation auxiliaries depend only on `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no added axiom, no `native_decide`. |
| The final assembly of the classification from cofinality, incomparability of candidates and faithfulness of detection sets | **Formal, conditional.** `OptimalityReduction.QuantumConnection.quantum_classification_given_structural_inputs` takes these three inputs as explicit hypotheses. |
| Necessity and the corrected characterization for arbitrary admissible targets (positive lift, product-vector refinement, mirror comparison, orbit incomparability), the S-lemma converse, the unique-source SDP, robustness, compactification and volume reversal | **Conventional proofs** in the manuscript, using the published decomposability and normal-form theorems. [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) lists each bridge that is not formalized. |
| 159 symbolic identities, the normal-form formulas, five exact primal–dual optima and two exact containment certificates | **Exact computation** with SymPy, [verification/](verification/); the SDP solver output is a floating-point illustration only. |

The canonical ellipsoid in Lean is the affine image of the unit ball read from the Pauli coefficients of an operator whose Bob marginal is maximally mixed, which is the ellipsoid of Milne et al. for such operators; every example is proved canonical, except the Class C comparison, which uses the actual fractional steering map.

## Prior work and priority

The family `W_p` is Example 2 of Milne, Jennings and Rudolph, who credit it to earlier work; only its use to separate the two readings is new. The fineness criterion and positive-remainder subtraction are due to Lewenstein, Kraus, Cirac and Horodecki; best separable approximations and product-vector subtraction to Lewenstein–Sanpera and Karnas–Lewenstein; best positive-part decompositions to Bruß et al.; semidefinite programs for optimal decompositions to Thiang, Raynal and Englert. A bounded search through 3 November 2026, including the works citing the source paper, found no earlier proof or counterexample. The claimed Lean proofs recorded in the Omega Institute's public repository for Conjectures 1 and 2 of Milne, Jennings, Jevtic and Rudolph ([PRIORITY_AND_NOVELTY.md](../../../PRIORITY_AND_NOVELTY.md)) concern a different paper (arXiv:1404.3951) and different statements; a search of that repository's issues and code on 3 November 2026 found no record of arXiv:1407.8440. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf), its [LaTeX source](manuscript.tex), the section files in [sections/](sections/) and the [figures](figures/).
- [lean/](lean/): the Lean project (nine content modules, the aggregate `Main.lean`, the selected-theorem script `AxiomAudit.lean` and the whole-project audit `ProjectAxiomAudit.lean`). [THEOREM_INDEX.md](THEOREM_INDEX.md) maps the mathematics to the declarations and [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) states the unconditional, conditional and unformalized scope.
- [verification/](verification/): the exact SymPy scripts and their frozen reports, the numerical SDP demonstration, the figure generator and the fresh [replay record](verification/replay/).
- [scripts/](scripts/): the audit checker, the exact-check runner and the full verification script.
- [Verification instructions](VERIFICATION.md), [authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
