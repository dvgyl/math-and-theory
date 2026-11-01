import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import QPermanentResearch.D2Orbit

/-! A reusable exact rank certificate from a nonsingular row minor. -/

namespace QPermanentResearch
open Module

theorem matrix_rank_eq_width_of_nonsingular_row_minor
    {K : Type*} [Field K] {m : Type*} [Fintype m] {n : ℕ}
    (V : Matrix m (Fin n) K) (rows : Fin n → m)
    (hdet : (V.submatrix rows id).det ≠ 0) : V.rank = n := by
  classical
  have hminor : Function.Injective (V.submatrix rows id).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((V.submatrix rows id).isUnit_iff_isUnit_det.mpr
        (isUnit_iff_ne_zero.mpr hdet))
  have hinj : Function.Injective V.mulVec := by
    intro x y h
    apply hminor
    ext i
    exact congrFun h (rows i)
  change finrank K (LinearMap.range V.mulVecLin) = n
  rw [LinearMap.finrank_range_of_inj hinj]
  simp

/-- The first two rows and the penultimate row of a mirrored orbit wrapper. -/
def d2OuterMinorRows (n : ℕ) : Fin 3 → Fin (n+4) :=
  ![(0 : Fin (n+2)).castSucc.castSucc,
    (0 : Fin (n+1)).succ.castSucc.castSucc,
    (Fin.last (n+2)).castSucc]

theorem d2OuterMinorRows_values (n : ℕ) :
    (fun i => (d2OuterMinorRows n i).val) = ![0, 1, n+2] := by
  ext i
  fin_cases i <;> rfl

theorem d2Wrap_outer_minor {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ) (a b c : ℝ) :
    (d2Wrap V a b c).submatrix (d2OuterMinorRows n) id =
      !![-a, b, c; -a, -b, c; a, b, c] := by
  ext i j
  fin_cases i
  · change d2Wrap V a b c ((0 : Fin (n+2)).castSucc.castSucc) j = ![-a, b, c] j
    rw [d2Wrap, appendRow_castSucc, appendRow_castSucc, prependRow_zero]
  · change d2Wrap V a b c ((0 : Fin (n+1)).succ.castSucc.castSucc) j = ![-a, -b, c] j
    rw [d2Wrap, appendRow_castSucc, appendRow_castSucc, prependRow_succ, prependRow_zero]
  · change d2Wrap V a b c ((Fin.last (n+2)).castSucc) j = ![a, b, c] j
    rw [d2Wrap, appendRow_castSucc, appendRow_last]

theorem d2Wrap_outer_minor_det {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ) (a b c : ℝ) :
    ((d2Wrap V a b c).submatrix (d2OuterMinorRows n) id).det = 4*a*b*c := by
  rw [d2Wrap_outer_minor]
  simp [Matrix.det_fin_three, Matrix.of_apply]
  ring

theorem d2Wrap_rank_three {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : (d2Wrap V a b c).rank = 3 := by
  apply matrix_rank_eq_width_of_nonsingular_row_minor _ (d2OuterMinorRows n)
  rw [d2Wrap_outer_minor_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) ha) hb) hc

end QPermanentResearch
