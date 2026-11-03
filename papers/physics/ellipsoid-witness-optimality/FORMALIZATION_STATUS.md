# Formalization status

This ledger is part of the mathematical claim, not an optional qualification.
The fresh replay in [verification/replay/](verification/replay/) records the
checked build and the whole-project axiom audit; [release-manifest.json](release-manifest.json)
records the source hashes.

## Fully formalized refutations and concrete theorems

The relevant matrices are genuine 4×4 complex matrices; states quantify over all
complex Hermitian positive-semidefinite trace-one matrices; block positivity
quantifies over all complex product vectors.

- The original equal-ellipsoid Class D counterexample and its strict detector
  inclusion, including an exact physical separating state.
- The same-negative-chirality proper-containment counterexample.
- The entire parameterized family: exact fineness and strict-fineness order,
  Class C/D status, geometric containment and equality, unique PSD subtraction
  coefficient and sharp simultaneous detector margin.
- Infinite counterexamples to sufficiency and nonoptimality in any surrounding
  set containing the finer mirror.
- Unique optimization within the explicitly defined axial one-parameter family.
  This statement does not quantify over every possible witness.
- The Class C strict comparison with incomparable geometric ellipsoids, including
  actual Pauli coefficients and a noncanonical fractional steering map.
- Bell-diagonal PSD iff inequalities and both ordinary/extraordinary normal-form
  positive-remainder identities. These certify arithmetic inside the forms.
- The sharp three-parameter mirror scalar interval and its width.
- General real 4×4 LMI soundness for the fractional map, including positive
  denominators and singular support constraints; exact diagonal containment iff.
- Every complex subspace of C²⊗C² with dimension at least two contains a nonzero
  product vector. The proof uses mathlib's algebraic closedness of C, an explicit
  determinant-pencil root, and explicit tensor factorization.

## Kernel-checked implications with substantive explicit hypotheses

`OptimalityReduction.QuantumConnection.quantum_classification_given_structural_inputs`
proves the optimality equivalence from:

1. membership of the candidate set in the feasible set;
2. a cofinal refinement into the candidate set for every feasible witness;
3. incomparability between candidates;
4. equality of normalized witnesses when their detection sets agree.

The theorem uses the actual matrix detector definitions. It does **not** prove
that all four hypotheses hold for arbitrary ellipsoid targets. Their analytic
proofs appear in the [manuscript](manuscript.pdf).

`finite_rank_one_refinement` and `rank_four_requires_at_most_three_steps` prove
termination, preservation of a positive remainder, and the counted step bound
from an explicit rank-drop hypothesis. They do **not** silently provide the
matrix pseudoinverse subtraction lemma. `ProductVector` proves the product-vector
existence input independently, but connecting that vector to the full PSD
rank-drop operation remains a separate bridge.

The interpolation identity is proved in any real module. Its applications to
cone preservation, feasible conditional states and chirality continuity remain
analytic arguments.

## Remaining bridges for a complete arbitrary-target classification in Lean

| Bridge | Present status |
|---|---|
| Two-qubit block-positive decomposability | Published theorem, cited and used analytically; not formalized here |
| Full Lorentz normal-form existence, including boundary forms | Published theorem; algebraic remainder certificates are checked, existence is not |
| Nonsingular witness marginals, whitening and filter/ellipsoid correspondence | Analytic proofs and primary references; not a complete Lean chain |
| Same-orbit incomparability | Complete analytic contraction argument; not fully formalized |
| Positive lift for arbitrary translated/singular targets | Analytic pseudoinverse proof; not formalized as a general matrix map theorem |
| PSD rank drop at τ=(v†Q⁺v)⁻¹ | Analytic proof; product-vector existence is separately checked |
| General normalized fineness iff PSD subtraction | Analytic cone-duality proof; explicit family and example implications are checked |
| S-lemma necessity | Published theorem; Lean checks certificate sufficiency, not this converse |
| Pseudoinverse metric equals the general ellipsoid image | Analytic linear algebra; the formal certificate uses the displayed support-and-metric set |
| Unique-source SDP, robustness ball, compactification, volume reversal | Analytic theorems and exact symbolic certificates where specified; not unified Lean statements |

There is no file claiming an unconditional theorem for the full arbitrary-target
classification. There are no custom axioms or proof placeholders hiding these
bridges. Completing them is a substantive further formalization project.

## Definition cautions

- `canonicalEllipsoid` is used for matrices whose canonicality is proved. The
  noncanonical Class C example has its own actual fractional map.
- `InSet` in the original counterexample file is restricted to canonical witnesses.
  The separate any-containing-set theorem transfers nonoptimality to the full
  intended surrounding set without requiring its other members to be canonical.
- The generic geometry module's `metricEnclosure` includes an explicit support
  projector condition. A pseudoinverse quadratic form by itself is insufficient
  for a planar target; the file proves a counterexample to that omission.
- A successful axiom audit certifies logical dependencies of the stated theorems.
  It does not discharge explicit hypotheses in a conditional theorem or establish
  publication novelty.
