import RadiusAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace SquareFlowerCompletion.Radius

theorem lower_of_add_log {u L : ℝ} (hu : 0 < u) (hL : 1 ≤ L)
    (h : L ≤ u+Real.log u) : L-Real.log L ≤ u := by
  by_cases hLu : L ≤ u
  · have hlog := Real.log_nonneg hL
    linarith
  · have huL : u < L := lt_of_not_ge hLu
    have hlog := Real.log_le_log hu huL.le
    linarith

theorem twice_log_shift_le (n : ℕ) (r : ℝ) (hr : 4 ≤ r)
    (hpower : r-1 ≤ (1+2/(r-3)^2)^n) :
    2*Real.log (r-3) ≤ 4*(n : ℝ)/(r-3)^2 := by
  have hx : 0 < r-3 := by linarith
  have hx2 : 0 < (r-3)^2 := sq_pos_of_pos hx
  have hbase : 0 < 1+2/(r-3)^2 := by positivity
  have hlog : Real.log (r-3) ≤ Real.log ((1+2/(r-3)^2)^n) :=
    Real.log_le_log hx ((by linarith : r-3 ≤ r-1).trans hpower)
  rw [Real.log_pow] at hlog
  have hlogbase : Real.log (1+2/(r-3)^2) ≤ 2/(r-3)^2 := by
    have h := Real.log_le_sub_one_of_pos hbase
    linarith
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hmul := mul_le_mul_of_nonneg_left hlogbase hn
  calc
    2*Real.log (r-3) ≤ 2*((n : ℝ)*(2/(r-3)^2)) := by linarith
    _ = 4*(n : ℝ)/(r-3)^2 := by ring

theorem log_scale_identity (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 4 ≤ r) :
    Real.log (4*(n : ℝ)/(r-3)^2) = Real.log (4*(n : ℝ))-2*Real.log (r-3) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < r-3 := by linarith
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  norm_num

theorem lower_of_power (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 4 ≤ r)
    (hpower : r-1 ≤ (1+2/(r-3)^2)^n) (hL : 1 ≤ Real.log (4*(n : ℝ))) :
    Real.log (4*(n : ℝ))-Real.log (Real.log (4*(n : ℝ))) ≤ 4*(n : ℝ)/(r-3)^2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < r-3 := by linarith
  have hu : 0 < 4*(n : ℝ)/(r-3)^2 := by positivity
  apply lower_of_add_log hu hL
  rw [log_scale_identity n hn r hr]
  have hlog := twice_log_shift_le n r hr hpower
  linarith

#print axioms lower_of_add_log
#print axioms twice_log_shift_le
#print axioms log_scale_identity
#print axioms lower_of_power
end SquareFlowerCompletion.Radius
