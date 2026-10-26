module
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
Definitions for the real q-permanent counterexamples.
The coordinate order is part of the definition: permutations are weighted by
their ordinary inversion count on Fin n, not by a conjugacy-invariant statistic.
-/

namespace MathAndTheory.QPermanent

open scoped BigOperators

/-- The number of inverted ordered pairs in the given coordinate order. -/
def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

/-- The genuine inversion-weighted q-permanent, summed over all permutations. -/
def qPermanent {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (q : R) : R :=
  ∑ σ : Equiv.Perm (Fin n), q ^ inversionCount σ * ∏ i : Fin n, A i (σ i)

/-- A scalar ring homomorphism commutes with the finite q-permanent expression. -/
theorem map_qPermanent {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (q : R) :
    f (qPermanent A q) = qPermanent (fun i j => f (A i j)) (f q) := by
  simp only [qPermanent, map_sum, map_mul, map_pow, map_prod]

end MathAndTheory.QPermanent
