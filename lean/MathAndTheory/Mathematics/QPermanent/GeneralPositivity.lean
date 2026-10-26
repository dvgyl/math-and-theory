module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import MathAndTheory.Mathematics.QPermanent.GeneralIndex

@[expose] public section

namespace MathAndTheory.QPermanent

open Matrix

def familyCore {R : Type*} [CommRing R] (a d : R) : Matrix (Fin 4) (Fin 4) R :=
  !![d, 0, a, 1;
     0, d, -1, a;
     a, -1, d, 0;
     1, a, 0, d]

theorem familyCore_isHermitian (a d : ℝ) : (familyCore a d).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [familyCore, Matrix.conjTranspose_apply]

theorem familyCore_quadratic_identity (a d : ℝ) (x : Fin 4 → ℝ) :
    d * (star x ⬝ᵥ (familyCore a d *ᵥ x)) =
      (d * x 0 + a * x 2 + x 3) ^ 2 +
      (d * x 1 - x 2 + a * x 3) ^ 2 +
      (d ^ 2 - a ^ 2 - 1) * ((x 2) ^ 2 + (x 3) ^ 2) := by
  simp [familyCore, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem familyCore_posDef (a d : ℝ) (hd : 0 < d) (hda : a ^ 2 + 1 < d ^ 2) :
    (familyCore a d).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (familyCore_isHermitian a d)
  intro x hx
  have hgap : 0 < d ^ 2 - a ^ 2 - 1 := by linarith
  have h₁ := sq_nonneg (d * x 0 + a * x 2 + x 3)
  have h₂ := sq_nonneg (d * x 1 - x 2 + a * x 3)
  have h₃ := sq_nonneg (x 2)
  have h₄ := sq_nonneg (x 3)
  have hid := familyCore_quadratic_identity a d x
  by_contra hnot
  have hq : star x ⬝ᵥ (familyCore a d *ᵥ x) ≤ 0 := le_of_not_gt hnot
  have hs : (x 2) ^ 2 + (x 3) ^ 2 = 0 := by
    have : 0 ≤ (d ^ 2 - a ^ 2 - 1) * ((x 2) ^ 2 + (x 3) ^ 2) :=
      mul_nonneg hgap.le (add_nonneg h₃ h₄)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hd.le hq]
  have hx2 : x 2 = 0 := by nlinarith
  have hx3 : x 3 = 0 := by nlinarith
  have hx0 : x 0 = 0 := by
    simp only [hx2, hx3, mul_zero, add_zero, sub_zero] at hid h₁ h₂
    have : (d * x 0) ^ 2 = 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hd.le hq]
    have : d * x 0 = 0 := sq_eq_zero_iff.mp this
    exact (mul_eq_zero.mp this).resolve_left hd.ne'
  have hx1 : x 1 = 0 := by
    simp only [hx2, hx3, hx0, mul_zero, zero_pow, add_zero, zero_add, sub_zero] at hid
    have : (d * x 1) ^ 2 = 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hd.le hq]
    have : d * x 1 = 0 := sq_eq_zero_iff.mp this
    exact (mul_eq_zero.mp this).resolve_left hd.ne'
  apply hx
  funext i
  fin_cases i <;> simp [hx0, hx1, hx2, hx3]

/-- Appending isolated identity coordinates preserves strict positivity. -/
theorem posDef_fromBlocks_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (m : ℕ) :
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact hA.isHermitian.fromBlocks (by simp) Matrix.isHermitian_one
  intro x hx
  have hid : star x ⬝ᵥ
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      star (x ∘ Sum.inr) ⬝ᵥ (x ∘ Sum.inr) := by
    simp [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
      Function.comp_def]
  rw [hid]
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    simpa [hl] using (Matrix.PosDef.one (n := Fin m) (R := ℝ)).dotProduct_mulVec_pos hr
  · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hl)
      (dotProduct_star_self_nonneg _)

/-- The manuscript's matrix with four active coordinates and an intervening identity block. -/
def familyMatrix (m : ℕ) (a d : ℝ) : Matrix (Fin (m + 4)) (Fin (m + 4)) ℝ :=
  (Matrix.fromBlocks (familyCore a d) 0 0 (1 : Matrix (Fin m) (Fin m) ℝ)).submatrix
    (familyIndex m).symm (familyIndex m).symm

theorem familyMatrix_posDef (m : ℕ) (a d : ℝ)
    (hd : 0 < d) (hda : a ^ 2 + 1 < d ^ 2) : (familyMatrix m a d).PosDef :=
  (posDef_fromBlocks_identity (familyCore_posDef a d hd hda) m).submatrix
    (familyIndex m).symm.injective

theorem familyMatrix_sqrt_posDef (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (familyMatrix m (Real.sqrt t) (Real.sqrt (t + 2))).PosDef := by
  apply familyMatrix_posDef
  · exact Real.sqrt_pos.mpr (by linarith)
  · rw [Real.sq_sqrt ht, Real.sq_sqrt (by linarith : 0 ≤ t + 2)]
    linarith

end MathAndTheory.QPermanent
