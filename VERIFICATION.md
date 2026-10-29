# Formal statement and verification scope

The package contains the complete proof source and an independent Comparator statement. The source came from commit `a6574b1bf6a591d81c3314d5333fc5da26712d6b` of `dvgyl/math-and-theory`.

The current package pins Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The proof, Solution, and Audit compile locally with warnings treated as errors and trust level zero. Challenge compiles with its two deliberate theorem placeholders. All fifteen local axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The full Palomar comparison and independent kernel checks remain pending. Earlier compiler records refer to different source bytes and a different toolchain. Those records are not included. A source hash inventory establishes file identity only. It does not establish proof acceptance.

For every integer `L ≥ 1`, define the catalyst local dimension as `n = 2^(4L)`. The same catalyst coefficients are used for every target dimension and target probability vector. Let `J` be a finite index type with decidable equality. Choose `j₀ : J`. Let `m = Fintype.card J`. For every `p : J → ℝ` with nonnegative values and sum one, the selected statements give a permutation of `J × Fin n`.

The permutation acts on each party separately. The combined local register on each party has dimension `mn`. The Hilbert space is the complex Euclidean space indexed by the pair of local registers. The proof library verifies that `bipartiteBasisPermutation σ τ` acts on product vectors as `localBasisPermutation σ` and `localBasisPermutation τ`.

Both displayed diagonal states have norm one. The first contains the catalyst and the target register fixed at `j₀`. The second contains the catalyst and the target Schmidt amplitudes `sqrt(p j)`. The norm of their complex inner product after the local permutations is at least `1 - 125m/L²`. This quantity is root fidelity `F`. The root infidelity is `1 - F`.

The second selected theorem gives the same bound as `1 - 2000m/(log₂ n)²`. The estimate is uniform over the target probability vector for fixed `m`. The bound retains its dependence on `m`. The catalyst is independent of `m`, but the stated error estimate is not.

The formalization uses the displayed Schmidt basis. It does not separately formalize a change from an arbitrary external basis to Schmidt form. It covers the dimension sequence `n = 2^(4L)`. It does not claim an optimal constant, an optimal dependence on `m`, a gate-complexity bound, or exact catalyst return.

`Challenge.lean` has two deliberate theorem holes. `Solution.lean` imports the complete proof source. The Challenge holes are excluded from the proof-status counts. `Audit.lean` requests fifteen axiom reports and checks the types of three main endpoints. The expected permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Run the official full Palomar preflight on the exact published submission commit before intake. Check the complete Solution, the independent Challenge comparison, every required kernel outcome, and the actual transitive axioms. A previous source build does not certify this port. Formal verification does not establish historical priority or expert peer review.
