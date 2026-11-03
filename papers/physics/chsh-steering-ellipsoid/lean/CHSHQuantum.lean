import CHSHAlgebra
import CHSHPhysical
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
Actual quantum CHSH operators, their generic Pauli linearization, and an exact
CHSH supremum theorem for the physical family constructed in GeneralAttainment.
The proof uses the elementary plane reduction, not an assumed Horodecki theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace CertifiedCHSH
noncomputable section

open CHSHPhysical (Mat QubitMat pauli tensor Density)

def spin (u : V) : QubitMat := ∑ i, (u i : ℂ) • pauli i

def bell (u u' v v' : V) : Mat :=
  tensor (spin u) (spin (v + v')) + tensor (spin u') (spin (v - v'))

def expect (ρ A : Mat) : ℂ := (ρ * A).trace

/-- The standard complex modulus, written directly to avoid topological imports. -/
def modulus (z : ℂ) : ℝ := Real.sqrt (Complex.normSq z)

theorem modulus_nonneg (z : ℂ) : 0 ≤ modulus z := Real.sqrt_nonneg _

theorem modulus_real (x : ℝ) : modulus (x : ℂ) = |x| := by
  unfold modulus
  rw [Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]


/-- Exact unit-direction CHSH values; no classical floor is added. -/
def values (ρ : Mat) : Set ℝ := {s | ∃ u u' v v' : V,
  Unit u ∧ Unit u' ∧ Unit v ∧ Unit v' ∧ s = modulus (expect ρ (bell u u' v v'))}

def beta (ρ : Mat) : ℝ := sSup (values ρ)

theorem expect_add (ρ A B : Mat) : expect ρ (A + B) = expect ρ A + expect ρ B := by
  simp only [expect, Matrix.mul_add, Matrix.trace_add]

theorem expect_smul (ρ A : Mat) (z : ℂ) : expect ρ (z • A) = z * expect ρ A := by
  simp only [expect, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem expect_sum (ρ : Mat) (F : Fin 3 → Mat) :
    expect ρ (∑ i, F i) = ∑ i, expect ρ (F i) := by
  simp only [expect, Matrix.mul_sum, Matrix.trace_sum]

theorem tensor_spin_expansion (u v : V) :
    tensor (spin u) (spin v) =
      ∑ i, ∑ j, ((u i * v j : ℝ) : ℂ) • tensor (pauli i) (pauli j) := by
  ext k l
  simp only [tensor, spin, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Pauli linearization for any complex matrix with the stated real readouts. -/
theorem spin_correlation (ρ : Mat) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : ∀ i j, expect ρ (tensor (pauli i) (pauli j)) = (C i j : ℂ))
    (u v : V) : expect ρ (tensor (spin u) (spin v)) = (dot u (C.mulVec v) : ℂ) := by
  rw [tensor_spin_expansion]
  simp only [expect_sum, expect_smul, hC]
  norm_num [dot, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

theorem bell_correlation (ρ : Mat) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : ∀ i j, expect ρ (tensor (pauli i) (pauli j)) = (C i j : ℂ))
    (u u' v v' : V) :
    expect ρ (bell u u' v v') =
      ((dot u (C.mulVec (v + v')) + dot u' (C.mulVec (v - v')) : ℝ) : ℂ) := by
  unfold bell
  rw [expect_add, spin_correlation ρ C hC, spin_correlation ρ C hC]
  simp only [Complex.ofReal_add]

theorem bell_norm_correlation (ρ : Mat) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : ∀ i j, expect ρ (tensor (pauli i) (pauli j)) = (C i j : ℂ))
    (u u' v v' : V) :
    modulus (expect ρ (bell u u' v v')) =
      |dot u (C.mulVec (v + v')) + dot u' (C.mulVec (v - v'))| := by
  rw [bell_correlation ρ C hC]
  exact modulus_real _

/-- Generic quantum upper-bound transfer from an orthogonal-plane certificate. -/
theorem bell_norm_le_of_plane (ρ : Mat) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : ∀ i j, expect ρ (tensor (pauli i) (pauli j)) = (C i j : ℂ))
    (m : ℝ) (hm : 0 ≤ m) (hp : PlaneBound C.mulVec m)
    (u u' v v' : V) (hu : Unit u) (hu' : Unit u') (hv : Unit v) (hv' : Unit v') :
    modulus (expect ρ (bell u u' v v')) ≤ 2 * Real.sqrt m := by
  rw [bell_norm_correlation ρ C hC]
  exact chsh_abs_le_of_plane C.mulVec m hm hp u u' v v' hu hu' hv hv'

end
end CertifiedCHSH
