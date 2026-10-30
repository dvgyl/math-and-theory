import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

open scoped BigOperators Matrix

noncomputable section
namespace UpperNoncollapse

/-- A flat, symmetric, trace-preserving orthogonal involution.
The physical instance is the product-Bell partial-transpose matrix. -/
structure FoldSystem (ι : Type*) [Fintype ι] [DecidableEq ι] where
  d : ℝ
  d_pos : 0 < d
  T : Matrix ι ι ℝ
  symmetric : ∀ i j, T i j = T j i
  involutive : T * T = 1
  row_sum : ∀ i, ∑ j, T i j = 1
  flat : ∀ i j, |T i j| = 1 / d
  card_eq : (Fintype.card ι : ℝ) = d ^ 2

namespace FoldSystem
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def apply (H : FoldSystem ι) (v : ι → ℝ) : ι → ℝ := H.T *ᵥ v

def fold (H : FoldSystem ι) (v : ι → ℝ) : ι → ℝ := fun i => |H.apply v i|

theorem apply_apply (H : FoldSystem ι) (v : ι → ℝ) :
    H.apply (H.apply v) = v := by
  simp [apply, Matrix.mulVec_mulVec, H.involutive]

theorem apply_one (H : FoldSystem ι) : H.apply (fun _ => 1) = fun _ => 1 := by
  funext i
  simpa [apply, Matrix.mulVec, dotProduct] using H.row_sum i

theorem flat_sq (H : FoldSystem ι) (i j : ι) : (H.T i j)^2 = 1 / H.d^2 := by
  have h := congrArg (fun x : ℝ => x^2) (H.flat i j)
  simpa [sq_abs, div_pow] using h

theorem apply_dot (H : FoldSystem ι) (v w : ι → ℝ) :
    (∑ i, H.apply v i * w i) = ∑ i, v i * H.apply w i := by
  simp only [apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [H.symmetric j i]
  ring

theorem apply_sq_sum (H : FoldSystem ι) (v : ι → ℝ) :
    (∑ i, H.apply v i ^ 2) = ∑ i, v i ^ 2 := by
  simpa only [pow_two, H.apply_apply] using H.apply_dot v (H.apply v)

theorem fold_sq_sum (H : FoldSystem ι) (v : ι → ℝ) :
    (∑ i, H.fold v i ^ 2) = ∑ i, v i ^ 2 := by
  simpa only [fold, sq_abs] using H.apply_sq_sum v

theorem apply_sum (H : FoldSystem ι) (v : ι → ℝ) :
    (∑ i, H.apply v i) = ∑ i, v i := by
  simpa only [H.apply_one, mul_one] using H.apply_dot v (fun _ => 1)

end FoldSystem
end UpperNoncollapse
