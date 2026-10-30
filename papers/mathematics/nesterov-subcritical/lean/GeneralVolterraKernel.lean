import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace GeneralNesterovExistence

def kernel (r t s : ℝ) : ℝ := (s - t ^ (1-r) * |s| ^ r) / (r-1)

lemma rpow_complement_mul {t : ℝ} (ht : 0 < t) (r : ℝ) :
    t ^ (1-r) * t ^ r = t := by
  rw [← Real.rpow_add ht]
  convert Real.rpow_one t using 1
  congr 1
  ring

lemma kernel_normalized {r t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    kernel r t s = t * (s/t - (s/t)^r) / (r-1) := by
  have hp : t ^ r ≠ 0 := (Real.rpow_pos_of_pos ht r).ne'
  have he : t ^ (1-r) = t / t ^ r := by
    apply (eq_div_iff hp).2
    exact rpow_complement_mul ht r
  rw [kernel, abs_of_nonneg hs, he, Real.div_rpow hs ht.le]
  congr 1
  field_simp [ht.ne', hp]
  ring

lemma kernel_nonneg {r t s : ℝ} (hr : 1 < r) (ht : 0 < t) (hs : s ∈ Icc 0 t) :
    0 ≤ kernel r t s := by
  rw [kernel_normalized ht hs.1]
  have hx0 : 0 ≤ s/t := div_nonneg hs.1 ht.le
  have hx1 : s/t ≤ 1 := (div_le_one ht).2 hs.2
  exact div_nonneg (mul_nonneg ht.le
    (sub_nonneg.mpr (Real.rpow_le_self_of_le_one hx0 hx1 hr.le))) (sub_pos.mpr hr).le

lemma kernel_le {r t s : ℝ} (hr : 1 < r) (ht : 0 < t) (hs : s ∈ Icc 0 t) :
    kernel r t s ≤ t-s := by
  rw [kernel_normalized ht hs.1, div_le_iff₀ (sub_pos.mpr hr)]
  have hx0 : 0 ≤ s/t := div_nonneg hs.1 ht.le
  have hh := one_add_mul_self_le_rpow_one_add (s := s/t-1) (by linarith) hr.le
  have heq : 1 + (s/t-1) = s/t := by ring
  rw [heq] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht.le
  have hcancel : t * (s/t) = s := by field_simp
  nlinarith

lemma kernel_continuous {r : ℝ} (hr : 1 < r) (t : ℝ) : Continuous (kernel r t) := by
  unfold kernel
  exact (continuous_id.sub (continuous_const.mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ r)).comp continuous_abs))).div_const (r-1)

lemma exponential_kernel_integral (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (t-s)*Real.exp (2*s)) =
      (Real.exp (2*t)-1-2*t)/4 := by
  have hd (s : ℝ) :
      HasDerivAt (fun s : ℝ => ((t-s)/2+1/4)*Real.exp (2*s))
        ((t-s)*Real.exp (2*s)) s := by
    convert (((hasDerivAt_const s t).sub (hasDerivAt_id s)).div_const 2 |>.add_const (1/4)).mul
      (((hasDerivAt_id s).const_mul 2).exp) using 1
    simp only [id_eq]
    ring
  have hi : IntervalIntegrable (fun s : ℝ => (t-s)*Real.exp (2*s)) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ => (t-s)*Real.exp (2*s))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi]
  simp only [sub_self, zero_div, zero_add, mul_zero, Real.exp_zero, sub_zero, mul_one]
  ring

lemma weighted_kernel_bound {r t : ℝ} (hr : 1 < r) (ht : 0 < t) :
    Real.exp (-2*t) * (∫ s in (0 : ℝ)..t, kernel r t s * Real.exp (2*s)) ≤ 1/4 := by
  have hmono : (∫ s in (0 : ℝ)..t, kernel r t s * Real.exp (2*s)) ≤
      ∫ s in (0 : ℝ)..t, (t-s)*Real.exp (2*s) := by
    apply intervalIntegral.integral_mono_on ht.le
      (((kernel_continuous hr t).mul (by fun_prop : Continuous (fun s : ℝ => Real.exp (2*s)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun s : ℝ => (t-s)*Real.exp (2*s))).intervalIntegrable _ _)
    intro s hs
    exact mul_le_mul_of_nonneg_right (kernel_le hr ht hs) (Real.exp_pos _).le
  rw [exponential_kernel_integral] at hmono
  have hprod : Real.exp (-2*t)*Real.exp (2*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hp := Real.exp_pos (-2*t)
  have hb := mul_le_mul_of_nonneg_left hmono hp.le
  nlinarith

lemma integral_kernel_bound {r t : ℝ} (hr : 1 < r) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, kernel r t s) ≤ t^2 := by
  have hm : (∫ s in (0 : ℝ)..t, kernel r t s) ≤ ∫ _s in (0 : ℝ)..t, t := by
    apply intervalIntegral.integral_mono_on ht.le
      ((kernel_continuous hr t).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro s hs
    exact (kernel_le hr ht hs).trans (by linarith [hs.1])
  simpa [pow_two] using hm

lemma exp_weight_square_le (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-2*t)*t^2 ≤ 1 := by
  have h : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hs : t^2 ≤ (Real.exp t)^2 := pow_le_pow_left₀ ht h 2
  have hh : Real.exp (-2*t)*(Real.exp t)^2 = 1 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  nlinarith [mul_le_mul_of_nonneg_left hs (Real.exp_pos (-2*t)).le]

end GeneralNesterovExistence
