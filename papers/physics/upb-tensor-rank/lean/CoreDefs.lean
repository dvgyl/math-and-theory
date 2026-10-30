import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
Shared definitions for the candidate PPT cone counterexample.
These definitions by themselves assert no research result.
-/
open scoped BigOperators Matrix ComplexOrder

namespace PPTCone

variable {A B : Type*}

/-- Partial transpose on the second local matrix factor. -/
def partialTranspose (R : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  fun i j => R (i.1, j.2) (j.1, i.2)

/-- The unnormalised pure-state positive matrix associated to a vector. -/
def pure (v : A × B → ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun i j => v i * star (v j)

/-- A vector has Schmidt rank at most two precisely when it is a sum of
at most two simple tensors. Zero and rank-one vectors are included. -/
def HasSR2 (v : A × B → ℂ) : Prop :=
  ∃ a₁ a₂ : A → ℂ, ∃ b₁ b₂ : B → ℂ,
    ∀ i j, v (i,j) = a₁ i * b₁ j + a₂ i * b₂ j

/-- The cone of positive matrices with Schmidt number at most two.
Nonnegative coefficients are absorbed into the vectors. -/
def IsSN2 [Fintype A] [Fintype B] (R : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ n : ℕ, ∃ v : Fin n → A × B → ℂ,
    (∀ k, HasSR2 (v k)) ∧ R = ∑ k, pure (v k)

/-- The Choi-matrix form of SP₂ + transpose ∘ SP₂. -/
def IsDSP2 [Fintype A] [Fintype B] (R : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ Q T, IsSN2 Q ∧ IsSN2 T ∧ R = Q + partialTranspose T

/-- A complex matrix subspace contains no nonzero product vector. -/
def NoProduct (S : Submodule ℂ (Matrix A B ℂ)) : Prop :=
  ∀ (u : A → ℂ) (v : B → ℂ),
    (fun i j => u i * v j) ∈ S →
    (fun i j => u i * v j) = 0

@[simp] theorem partialTranspose_apply (R : Matrix (A × B) (A × B) ℂ)
    (i j : A × B) :
    partialTranspose R i j = R (i.1, j.2) (j.1, i.2) := rfl

@[simp] theorem partialTranspose_involutive (R : Matrix (A × B) (A × B) ℂ) :
    partialTranspose (partialTranspose R) = R := by
  ext i j
  rfl

@[simp] theorem partialTranspose_add (R T : Matrix (A × B) (A × B) ℂ) :
    partialTranspose (R + T) = partialTranspose R + partialTranspose T := by
  ext i j
  rfl

@[simp] theorem partialTranspose_sub (R T : Matrix (A × B) (A × B) ℂ) :
    partialTranspose (R - T) = partialTranspose R - partialTranspose T := by
  ext i j
  rfl

@[simp] theorem partialTranspose_zero :
    partialTranspose (0 : Matrix (A × B) (A × B) ℂ) = 0 := rfl

@[simp] theorem pure_zero : pure (0 : A × B → ℂ) = 0 := by
  ext i j
  simp [pure]

end PPTCone
