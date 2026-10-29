import RadiusExactAlgebra
import PositiveLambert

noncomputable section
namespace SquareFlowerCompletion.Radius

theorem exact_power_log_bound (n : ℕ) (r : ℝ) (hr : 3 ≤ r)
    (hpower : r-1 ≤ (1+2/(r-2)^2)^n) :
    (r-2)^2 * Real.log ((r-2)^2) < 4*(n : ℝ) := by
  have hx : 0 < r-2 := by linarith
  have hy : 0 < (r-2)^2 := sq_pos_of_pos hx
  have hb : 0 < 1+2/(r-2)^2 := by positivity
  have hl : Real.log (r-2) < Real.log ((1+2/(r-2)^2)^n) :=
    (Real.log_lt_log hx (by linarith : r-2 < r-1)).trans_le
      (Real.log_le_log (by linarith : 0 < r-1) hpower)
  rw [Real.log_pow] at hl
  have hbase : Real.log (1+2/(r-2)^2) ≤ 2/(r-2)^2 := by
    have h := Real.log_le_sub_one_of_pos hb
    linarith
  have hm := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hlogy : Real.log ((r-2)^2) < 4*(n : ℝ)/(r-2)^2 := by
    rw [Real.log_pow]
    calc
      _ < 2*((n : ℝ)*(2/(r-2)^2)) := by linarith
      _ = _ := by ring
  simpa [mul_comm] using (lt_div_iff₀ hy).mp hlogy

theorem square_lt_lambert_scale {s y : ℝ} (hs : 0 < s) (hy : 0 < y)
    (h : y * Real.log y < s) : y < s / positiveLambert s := by
  by_contra hnot
  have he : Real.exp (positiveLambert s) ≤ y := by
    rw [exp_positiveLambert hs]
    exact le_of_not_gt hnot
  have hl : positiveLambert s ≤ Real.log y := by
    have hh := Real.log_le_log (Real.exp_pos (positiveLambert s)) he
    simpa using hh
  have hp := positiveLambert_spec hs
  have h1 := mul_le_mul_of_nonneg_left he hp.1.le
  have h2 := mul_le_mul_of_nonneg_right hl hy.le
  nlinarith [hp.2]

theorem bracket_root_strict_global_bound (n : ℕ) (z : ℂ) (hn : 0 < n)
    (hroot : bracket n z = 0) :
    ‖z‖ < 2 + Real.sqrt (4*(n : ℝ)/positiveLambert (4*(n : ℝ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < 4*(n : ℝ) := by positivity
  by_cases hr : 3 ≤ ‖z‖
  · have hy : 0 < (‖z‖-2)^2 := sq_pos_of_pos (by linarith)
    have hlog := exact_power_log_bound n ‖z‖ hr (bracket_root_exact_power n z hroot hr)
    have hsq := square_lt_lambert_scale hs hy hlog
    have hsqrt := Real.lt_sqrt_of_sq_lt hsq
    linarith
  · have hexp : 1 < 4*(n : ℝ)/positiveLambert (4*(n : ℝ)) := by
      rw [← exp_positiveLambert hs]
      exact Real.one_lt_exp_iff.mpr (positiveLambert_spec hs).1
    have hsqrt : 1 < Real.sqrt (4*(n : ℝ)/positiveLambert (4*(n : ℝ))) :=
      (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hexp)
    linarith

theorem actual_graph_root_strict_global_bound (n : ℕ) (z : ℂ) (hn : 0 < n)
    (hroot : (Counting.complexDominationPolynomial n).eval z = 0) :
    ‖z‖ < 2 + Real.sqrt (4*(n : ℝ)/positiveLambert (4*(n : ℝ))) := by
  by_cases hz : z = 0
  · simp only [hz, norm_zero]
    positivity
  · have hb : bracket n z = 0 := by
      have h := (Counting.eval_eq_zero_iff_bracket hz).mp hroot
      simpa [bracket,A,B] using h
    exact bracket_root_strict_global_bound n z hn hb

#print axioms exact_power_log_bound
#print axioms square_lt_lambert_scale
#print axioms bracket_root_strict_global_bound
#print axioms actual_graph_root_strict_global_bound
end SquareFlowerCompletion.Radius
