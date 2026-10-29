import DerivativeA
import TransferLimitA

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

theorem uniform_mul_one {S : Set ℂ} (F G : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (M : ℝ)
    (hF : TendstoUniformlyOn F f atTop S)
    (hG : TendstoUniformlyOn G (fun _ => 1) atTop S)
    (hf : ∀ v ∈ S, ‖f v‖ ≤ M) :
    TendstoUniformlyOn (fun n v => F n v * G n v) f atTop S := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  have hC : 0 < |M| + 1 := by positivity
  have htol : 0 < min (1 : ℝ) (η / 2) := lt_min (by norm_num) (half_pos hη)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hF) _ htol,
    (Metric.tendstoUniformlyOn_iff.1 hG) (η / (2 * (|M| + 1))) (div_pos hη (by positivity))] with n hFn hGn v hv
  have hFe : ‖F n v - f v‖ < min (1 : ℝ) (η / 2) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hFn v hv
  have hGe : ‖G n v - 1‖ < η / (2 * (|M| + 1)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hGn v hv
  have hFb : ‖F n v‖ ≤ |M| + 1 := by
    have h := norm_add_le (F n v - f v) (f v)
    rw [sub_add_cancel] at h
    linarith [hf v hv, le_abs_self M, min_le_left (1 : ℝ) (η / 2)]
  have hprod : (|M| + 1) * ‖G n v - 1‖ < η / 2 := by
    have h := (lt_div_iff₀ (show 0 < 2 * (|M| + 1) by positivity)).mp hGe
    nlinarith
  calc
    dist (f v) (F n v * G n v) = ‖F n v * (G n v - 1) + (F n v - f v)‖ := by
      rw [dist_eq_norm, norm_sub_rev]
      congr 1
      ring
    _ ≤ ‖F n v‖ * ‖G n v - 1‖ + ‖F n v - f v‖ := by
      simpa only [norm_mul] using norm_add_le (F n v * (G n v - 1)) (F n v - f v)
    _ ≤ (|M| + 1) * ‖G n v - 1‖ + ‖F n v - f v‖ := by gcongr
    _ < η := by linarith [hFe.trans_le (min_le_right (1 : ℝ) (η / 2))]

theorem uniform_derivativeFactor (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun n v => derivativeFactor (lam n) (reciprocalCoordinate (lam n) v) v)
      (fun _ => 1) atTop (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have hnorm := lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd
  have hε := epsilon_tendsto_zero logScale lam logScale_tendsto_atTop hd
  have hi : Tendsto (fun n => ‖lam n‖⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hnorm
  have hden : Tendsto (fun n => ‖lam n‖ - (1 / 4 : ℝ)) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(1 / 4 : ℝ)) hnorm
  have hid : Tendsto (fun n => (‖lam n‖ - (1 / 4 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have h24 : Tendsto (fun n => (24 : ℝ) * epsilon (lam n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hε :
      Tendsto (fun n => (24 : ℝ) * epsilon (lam n)) atTop (𝓝 (24 * 0)))
  have hr : Tendsto (fun n => (1 / 4 : ℝ) / ‖lam n‖) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds.mul hi :
      Tendsto (fun n => (1 / 4 : ℝ) * ‖lam n‖⁻¹) atTop (𝓝 ((1 / 4 : ℝ) * 0)))
  have h1 : Tendsto (fun n => (1 : ℝ) + 24 * epsilon (lam n)) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add h24 :
      Tendsto (fun n => (1 : ℝ) + 24 * epsilon (lam n)) atTop (𝓝 (1 + 0)))
  have hE : Tendsto (fun n =>
      1 / (‖lam n‖ - (1 / 4 : ℝ)) + 24 * epsilon (lam n) +
        ((1 / 4 : ℝ) / ‖lam n‖) * (1 + 24 * epsilon (lam n))) atTop (𝓝 0) := by
    simpa only [one_div, zero_add, zero_mul, add_zero] using (hid.add h24).add (hr.mul h1)
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  filter_upwards [hnorm.eventually_gt_atTop (1 / 4),
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hE.eventually (gt_mem_nhds hη)] with n hn hεn hEn v hv
  have hvnorm : ‖v‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hw := reciprocalCoordinate_bound (lam n) v hvnorm
  have hwsmall : ‖reciprocalCoordinate (lam n) v‖ ≤ (1 / 16 : ℝ) := hw.trans hεn.le
  have hlocal := norm_derivativeFactor_sub_one_le hwsmall (hvnorm.trans_lt hn)
  have hinv : 1 / (‖lam n‖ - ‖v‖) ≤ 1 / (‖lam n‖ - (1 / 4 : ℝ)) :=
    one_div_le_one_div_of_le (sub_pos.mpr hn) (by linarith)
  calc
    dist 1 (derivativeFactor (lam n) (reciprocalCoordinate (lam n) v) v) =
        ‖derivativeFactor (lam n) (reciprocalCoordinate (lam n) v) v - 1‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    _ ≤ _ := hlocal
    _ ≤ 1 / (‖lam n‖ - (1 / 4 : ℝ)) + 24 * epsilon (lam n) +
        ((1 / 4 : ℝ) / ‖lam n‖) * (1 + 24 * epsilon (lam n)) := by gcongr
    _ < η := hEn

def AD (n : ℕ) (lam v : ℂ) : ℂ := A n lam v * derivativeFactor lam (reciprocalCoordinate lam v) v

theorem uniform_AD (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    TendstoUniformlyOn (fun n v => AD n (lam n) v) (fun v => -Complex.exp v) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  apply uniform_mul_one (fun n v => A n (lam n) v)
    (fun n v => derivativeFactor (lam n) (reciprocalCoordinate (lam n) v) v)
    (fun v => -Complex.exp v) (Real.exp (1 / 4)) (uniform_A lam hd he) (uniform_derivativeFactor lam hd)
  intro v hv
  have hvnorm : ‖v‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  rw [norm_neg, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm v).trans hvnorm)

#print axioms uniform_derivativeFactor
#print axioms uniform_AD
end Transfer
end SquareFlowerCompletion
