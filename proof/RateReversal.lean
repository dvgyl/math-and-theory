module
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import PermutationCompat
public import PositiveRateMatrices
public import BranchCumulants

@[expose] public section

/-!
Reversing the chosen cycle orientation preserves the rate generator and
exchanges clockwise and anticlockwise products. The third/first cumulant
ratio is therefore unchanged. No sign assumption on the affinity is used.
-/

open scoped BigOperators
open Equiv Polynomial

namespace UnicyclicReversal

noncomputable section

open UnicyclicDeterminant UnicyclicCumulant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem rateMatrix_reversal [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v : ι → ℝ) (s : ℝ) :
    rateMatrix σ⁻¹ (fun j => v (σ⁻¹ j)) (fun j => u (σ⁻¹ j)) s =
      rateMatrix σ u v s := by
  ext i j
  have hf :
      (if j = σ⁻¹ i then -u (σ⁻¹ i) else 0) =
        (if i = σ j then -u j else 0) := by
    by_cases hij : i = σ j
    · subst i
      simp
    · have hji : j ≠ σ⁻¹ i := by
        intro h
        apply hij
        simpa using (congrArg σ h).symm
      simp [-Perm.coe_inv, hij,hji]
  have hb :
      (if i = σ⁻¹ j then -v (σ⁻¹ j) else 0) =
        (if j = σ i then -v i else 0) := by
    by_cases hji : j = σ i
    · subst j
      simp
    · have hij : i ≠ σ⁻¹ j := by
        intro h
        apply hji
        simpa using (congrArg σ h).symm
      simp [-Perm.coe_inv, hij,hji]
  simp only [rateMatrix,ringMatrix,inv_inv,UnicyclicPerm.inv_apply_apply]
  rw [hf,hb]
  have hd : s+v (σ⁻¹ j)+u j = s+u j+v (σ⁻¹ j) := by ring
  rw [hd]
  ring

theorem ratePolynomial_reversal (σ : Perm ι) (u v : ι → ℝ) :
    (-(rateMatrix σ⁻¹ (fun j => v (σ⁻¹ j)) (fun j => u (σ⁻¹ j)) 0)).charpoly =
      (-(rateMatrix σ u v 0)).charpoly := by
  rw [rateMatrix_reversal]

theorem rate_coefficient_skewness_reversal (σ : Perm ι) (u v : ι → ℝ) :
    let P := (-(rateMatrix σ u v 0)).charpoly
    let P' := (-(rateMatrix σ⁻¹ (fun j => v (σ⁻¹ j))
      (fun j => u (σ⁻¹ j)) 0)).charpoly
    third (P'.coeff 1) (P'.coeff 2) (P'.coeff 3)
        (∏ j, v (σ⁻¹ j)) (∏ j, u (σ⁻¹ j)) /
      first (P'.coeff 1) (∏ j, v (σ⁻¹ j)) (∏ j, u (σ⁻¹ j)) =
    third (P.coeff 1) (P.coeff 2) (P.coeff 3) (∏ j, u j) (∏ j, v j) /
      first (P.coeff 1) (∏ j, u j) (∏ j, v j) := by
  dsimp only
  simp only [rateMatrix_reversal σ u v 0, Equiv.prod_comp]
  exact skewness_swap _ _ _ _ _

#print axioms rateMatrix_reversal
#print axioms ratePolynomial_reversal
#print axioms rate_coefficient_skewness_reversal

end
end UnicyclicReversal
