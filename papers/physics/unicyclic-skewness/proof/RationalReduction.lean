import ScalarCertificate
import LogRelaxation

/-!
The logarithmic uncertainty premise is explicit. This file does not assert
that arbitrary Markov rates supply that premise or the spectral moments.
-/
namespace UnicyclicReduction
noncomputable section
set_option maxHeartbeats 1000000

theorem rational_constraint {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (htur : (1-r^2)/2 + r/Real.log ((1+r)/(1-r)) ≤ t^2) :
    0 ≤ UnicyclicScalar.R t (r^2) := by
  have hm : 0 < 1-r := by linarith
  have hs : 0 < 1-r^2 := by nlinarith
  have hz0 : 0 ≤ r^2 := sq_nonneg r
  have hz1 : r^2 ≤ 1 := by nlinarith
  have hd : 0 < UnicyclicScalar.D (r^2) := UnicyclicScalar.D_pos hz0 hz1
  let L := Real.log ((1+r)/(1-r))
  have hL : 0 < L := by
    apply Real.log_pos
    apply (one_lt_div hm).mpr
    linarith
  have hu := UnicyclicLog.log_ratio_upper (le_of_lt hr0) hr1
  have heq :
      2*r+(2/3 : ℝ)*r^3+(2/5 : ℝ)*r^5+2*r^7/(7*(1-r^2)) =
        2*r*UnicyclicScalar.D (r^2)/(105*(1-r^2)) := by
    dsimp [UnicyclicScalar.D]
    field_simp [ne_of_gt hs]
    ring
  rw [heq] at hu
  have hU : L * (105*(1-r^2)) ≤ 2*r*UnicyclicScalar.D (r^2) :=
    (le_div_iff₀ (mul_pos (by norm_num) hs)).mp hu
  have hT : 2*r ≤ L*(2*t^2-1+r^2) := by
    have hdiv : r/L ≤ t^2-(1-r^2)/2 := by
      change (1-r^2)/2 + r/L ≤ t^2 at htur
      linarith only [htur]
    have hh := (div_le_iff₀ hL).mp hdiv
    nlinarith only [hh]
  have hTD := mul_le_mul_of_nonneg_right hT (le_of_lt hd)
  have hid : L * UnicyclicScalar.R t (r^2) =
      L*(2*t^2-1+r^2)*UnicyclicScalar.D (r^2) - L*(105*(1-r^2)) := by
    dsimp [UnicyclicScalar.R]
    ring
  have hh : 0 ≤ L * UnicyclicScalar.R t (r^2) := by
    linarith only [hTD,hU,hid]
  exact nonneg_of_mul_nonneg_right hh hL

theorem lower_bound_from_log_uncertainty {r t p3 : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htur : (1-r^2)/2 + r/Real.log ((1+r)/(1-r)) ≤ t^2)
    (hp3 : p3 ≤ t^3) :
    -(1/16 : ℝ) ≤
      (3*t^4-2*p3+(1-r^2)*((1/2 : ℝ)-(3/2 : ℝ)*t^2))/(r^2) := by
  exact UnicyclicScalar.skewness_scalar_bound ht0 ht1 (sq_pos_of_pos hr0)
    (by nlinarith) (rational_constraint hr0 hr1 htur) hp3

#print axioms lower_bound_from_log_uncertainty
end
end UnicyclicReduction
