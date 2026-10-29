import RootEndpointScale
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
namespace SquareFlowerCompletion.RealCompanion

theorem endpoint_log_plus_error {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1/4) :
    |Real.log (1+s)-s| ≤ 2*s^2 := by
  have hsmall : |(-s)| < 1 := by rw [abs_neg,abs_of_nonneg hs0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hsmall 1
  have hbase : |Real.log (1+s)-s| ≤ s^2/(1-s) := by
    simpa [Finset.sum_range_succ,abs_of_nonneg hs0,add_comm,sub_eq_add_neg] using h
  have hfrac : s^2/(1-s) ≤ 2*s^2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-s)).mpr
    nlinarith [mul_nonneg (sq_nonneg s) (by linarith : 0 ≤ 1-2*s)]
  exact hbase.trans hfrac

theorem endpoint_log_minus_error {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1/4) :
    |Real.log (1-s)+s| ≤ 2*s^2 := by
  have hsmall : |s| < 1 := by rw [abs_of_nonneg hs0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hsmall 1
  have hbase : |Real.log (1-s)+s| ≤ s^2/(1-s) := by
    simpa [Finset.sum_range_succ,abs_of_nonneg hs0,add_comm] using h
  have hfrac : s^2/(1-s) ≤ 2*s^2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-s)).mpr
    nlinarith [mul_nonneg (sq_nonneg s) (by linarith : 0 ≤ 1-2*s)]
  exact hbase.trans hfrac

theorem scaled_endpoint_square_bound {n : ℕ} (hn : 0 < n) {s C : ℝ}
    (hs0 : 0 ≤ s) (hC : 0 ≤ C) (hscale : (n:ℝ)*s ≤ C) :
    (n:ℝ)*s^2 ≤ C^2/(n:ℝ) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ hN).mpr
  have hp := mul_nonneg (sub_nonneg.mpr hscale)
    (add_nonneg hC (mul_nonneg hN.le hs0))
  nlinarith

theorem scaled_endpoint_log_errors {n : ℕ} (hn : 0 < n) {s C : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1/4) (hC : 0 ≤ C) (hscale : (n:ℝ)*s ≤ C) :
    |(n:ℝ)*Real.log (1+s)-(n:ℝ)*s| ≤ 2*C^2/(n:ℝ) ∧
    |(n:ℝ)*Real.log (1-s)+(n:ℝ)*s| ≤ 2*C^2/(n:ℝ) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hsq := scaled_endpoint_square_bound hn hs0 hC hscale
  constructor
  · rw [← mul_sub,abs_mul,abs_of_pos hN]
    have hm := mul_le_mul_of_nonneg_left (endpoint_log_plus_error hs0 hs1) hN.le
    calc
      (n:ℝ)*|Real.log (1+s)-s| ≤ (n:ℝ)*(2*s^2) := hm
      _ = 2*((n:ℝ)*s^2) := by ring
      _ ≤ 2*(C^2/(n:ℝ)) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 2*C^2/(n:ℝ) := by ring
  · rw [← mul_add,abs_mul,abs_of_pos hN]
    have hm := mul_le_mul_of_nonneg_left (endpoint_log_minus_error hs0 hs1) hN.le
    calc
      (n:ℝ)*|Real.log (1-s)+s| ≤ (n:ℝ)*(2*s^2) := hm
      _ = 2*((n:ℝ)*s^2) := by ring
      _ ≤ 2*(C^2/(n:ℝ)) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 2*C^2/(n:ℝ) := by ring

theorem root_endpoint_log_errors {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Ioo 1 2) (hF : F n t = 0) :
    |(n:ℝ)*Real.log (1+endpointS t)-(n:ℝ)*endpointS t| ≤
        8*(Real.log 3)^2/(n:ℝ) ∧
    |(n:ℝ)*Real.log (1-endpointS t)+(n:ℝ)*endpointS t| ≤
        8*(Real.log 3)^2/(n:ℝ) := by
  have hs := endpointS_bounds ht
  have hC : 0 ≤ 2*Real.log 3 := by positivity
  have h := scaled_endpoint_log_errors hn hs.1.le hs.2 hC (root_scaled_endpointS_bound ht hF)
  convert h using 2 <;> ring

#print axioms endpoint_log_plus_error
#print axioms endpoint_log_minus_error
#print axioms scaled_endpoint_square_bound
#print axioms scaled_endpoint_log_errors
#print axioms root_endpoint_log_errors
end SquareFlowerCompletion.RealCompanion
