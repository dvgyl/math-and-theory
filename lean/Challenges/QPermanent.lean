module
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Da Fonseca's 2010 real positive-definite extension asks for strict increase
of the inversion-weighted q-permanent on a half-line starting at or below -1.
The coordinate order is part of this definition. The statements below
refute that extension and give a negative derivative at every prescribed q > 1.
-/
@[expose] public section
noncomputable section
namespace QPermanentProblem
open scoped BigOperators Matrix

def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

def qPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), q ^ inversions σ * ∏ i : Fin n, A i (σ i)

def witness : Matrix (Fin 5) (Fin 5) ℝ :=
  !![5, 0, 0, 4, 1;
     0, 5, 0, -1, 4;
     0, 0, 1, 0, 0;
     4, -1, 0, 5, 0;
     1, 4, 0, 0, 5]

theorem finite_counterexample :
    witness.PosDef ∧
    (∀ q : ℝ, qPermanent witness q =
      625 + 25*q^3 + 800*q^5 + 25*q^7 + q^8*(q-16)^2) ∧
    qPermanent witness 14 = 8968822249 ∧
    qPermanent witness 15 = 7441960000 ∧
    deriv (qPermanent witness) 15 = -1563030000 := by
  sorry

theorem extended_conjecture_false :
    ¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef → (∃ i j, i ≠ j ∧ A i j ≠ 0) →
      ∃ ε : ℝ, ε ≤ -1 ∧ StrictMonoOn (qPermanent A) (Set.Ioi ε)) := by
  sorry

theorem negative_derivative_at_every_parameter :
    ∀ r : ℝ, 1 < r →
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      5 ≤ n ∧ A.PosDef ∧ deriv (qPermanent A) r < 0 := by
  sorry

theorem dense_correlation_counterexamples :
    ∀ r : ℝ, 1 < r →
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef ∧ (∀ i, A i i = 1) ∧ (∀ i j, A i j ≠ 0) ∧
        deriv (qPermanent A) r < 0 := by
  sorry

theorem integer_counterexamples :
    ∀ r : ℝ, 1 < r →
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
      Matrix.PosDef (fun i j => (A i j : ℝ)) ∧
      deriv (qPermanent (fun i j => (A i j : ℝ))) r < 0 := by
  sorry

end QPermanentProblem
