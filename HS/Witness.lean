module
public import HS.Definitions
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped BigOperators ComplexConjugate

set_option autoImplicit false

namespace HS

/-- An unnormalized Higuchi--Sudbery vector. Its six nonzero amplitudes
are two copies each of `2`, `-1 + i sqrt 3`, and `-1 - i sqrt 3`. -/
noncomputable def hsUnnormalized : Fin 16 → ℂ :=
  ![0, 0, 0, 2, 0, ⟨-1, Real.sqrt 3⟩, ⟨-1, -Real.sqrt 3⟩, 0,
    0, ⟨-1, -Real.sqrt 3⟩, ⟨-1, Real.sqrt 3⟩, 0, 2, 0, 0, 0]

noncomputable def hsScale : ℝ := (Real.sqrt 24)⁻¹

/-- A normalized four-qubit pure state attaining the bound. -/
noncomputable def hsState (i : Fin 16) : ℂ := (hsScale : ℂ) * hsUnnormalized i

noncomputable def hsMarginal : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(1 / 6 : ℂ), 0, 0, 0],
    ![0, (1 / 3 : ℂ), (-1 / 6 : ℂ), 0],
    ![0, (-1 / 6 : ℂ), (1 / 3 : ℂ), 0],
    ![0, 0, 0, (1 / 6 : ℂ)]]

def hsMarginalUnnormalized : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![4, 0, 0, 0], ![0, 8, -4, 0], ![0, -4, 8, 0], ![0, 0, 0, 4]]

theorem hsScale_sq : hsScale ^ 2 = (1 / 24 : ℝ) := by
  rw [hsScale, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 24)]
  norm_num

theorem stateNormSq_real_scale (c : ℝ) (z : Fin 16 → ℂ) :
    stateNormSq (fun i => (c : ℂ) * z i) = c ^ 2 * stateNormSq z := by
  simp [stateNormSq, Complex.normSq_mul, Complex.normSq_ofReal, Finset.mul_sum, pow_two]

theorem hsUnnormalized_norm : stateNormSq hsUnnormalized = 24 := by
  norm_num [stateNormSq, hsUnnormalized, Fin.sum_univ_succ, Complex.normSq_apply]

theorem hsState_normalized : stateNormSq hsState = 1 := by
  change stateNormSq (fun i => (hsScale : ℂ) * hsUnnormalized i) = 1
  rw [stateNormSq_real_scale, hsUnnormalized_norm, hsScale_sq]
  norm_num

theorem reduced_real_scale (cut : Fin 3) (c : ℝ) (z : Fin 16 → ℂ) :
    reduced cut (fun i => (c : ℂ) * z i) =
      fun r s => ((c ^ 2 : ℝ) : ℂ) * reduced cut z r s := by
  ext r s : 2
  simp [reduced, flatten, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum, pow_two, mul_comm, mul_left_comm, mul_assoc]

set_option maxHeartbeats 0 in
theorem hsUnnormalized_reduced (cut : Fin 3) :
    reduced cut hsUnnormalized = hsMarginalUnnormalized := by
  have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases cut <;> ext r s : 2 <;> fin_cases r <;> fin_cases s <;>
    apply Complex.ext <;>
    norm_num [reduced, flatten, flattenIndex, hsUnnormalized, hsMarginalUnnormalized,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem hsState_reduced (cut : Fin 3) : reduced cut hsState = hsMarginal := by
  change reduced cut (fun i => (hsScale : ℂ) * hsUnnormalized i) = hsMarginal
  rw [reduced_real_scale, hsUnnormalized_reduced, hsScale_sq]
  ext r s : 2
  fin_cases r <;> fin_cases s <;> norm_num [hsMarginal, hsMarginalUnnormalized]

end HS
