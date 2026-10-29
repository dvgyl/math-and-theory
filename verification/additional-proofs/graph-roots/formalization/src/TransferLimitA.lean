import ReciprocalModel
import UniformExp
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

theorem uniform_div_of_bound {S : Set ℂ} (g : ℂ → ℂ) (C : ℝ)
    (hg : ∀ v ∈ S, ‖g v‖ ≤ C) (lam : ℕ → ℂ)
    (hlam : Tendsto (fun n => ‖lam n‖) atTop atTop) :
    TendstoUniformlyOn (fun n v => g v / lam n) (fun _ => 0) atTop S := by
  have hi : Tendsto (fun n => ‖lam n‖⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlam
  have hc : Tendsto (fun n => C / ‖lam n‖) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hi : Tendsto (fun n => C * ‖lam n‖⁻¹) atTop (𝓝 (C * 0)))
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  filter_upwards [hc.eventually (gt_mem_nhds hη)] with n hn v hv
  calc
    dist 0 (g v / lam n) = ‖g v‖ / ‖lam n‖ := by simp only [dist_eq_norm, zero_sub, norm_neg, norm_div]
    _ ≤ C / ‖lam n‖ := div_le_div_of_nonneg_right (hg v hv) (norm_nonneg _)
    _ < η := hn

theorem uniform_perturbation (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    TendstoUniformlyOn (fun n v => perturbation n (lam n) v) (fun _ => 0) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have hf : TendstoUniformlyOn (fun n v => (v ^ 2 / 2) / lam n) (fun _ => 0) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
    apply uniform_div_of_bound (fun v => v ^ 2 / 2) (1 / 32) _ lam
      (lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd)
    intro v hv
    have hvnorm : ‖v‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    norm_num [norm_div, norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg v) hvnorm 2
    nlinarith
  have hr := uniform_actual_log_remainder lam hd he
  convert hf.add hr using 1
  · funext n v
    dsimp [perturbation, logError]
    rw [div_div]
  · funext v
    simp

theorem uniform_A (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    TendstoUniformlyOn (fun n v => A n (lam n) v) (fun v => -Complex.exp v) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have hδ := uniform_perturbation lam hd he
  have hExp := uniform_exp_add (fun n v => perturbation n (lam n) v) (1 / 4) hδ
  have hi : Tendsto (fun n => ‖lam n‖⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd)
  have hsmall : Tendsto (fun n => Real.exp ((1 / 4 : ℝ) + 1) * ((1 / 4 : ℝ) / ‖lam n‖)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hi) :
        Tendsto (fun n => Real.exp ((1 / 4 : ℝ) + 1) * ((1 / 4 : ℝ) * ‖lam n‖⁻¹)) atTop
          (𝓝 (Real.exp ((1 / 4 : ℝ) + 1) * ((1 / 4 : ℝ) * 0))))
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  filter_upwards [he, eventually_ge_atTop 1,
    (Metric.tendstoUniformlyOn_iff.1 hδ) 1 (by norm_num),
    (Metric.tendstoUniformlyOn_iff.1 hExp) (η / 2) (half_pos hη),
    hsmall.eventually (gt_mem_nhds (half_pos hη))] with n hn hnpos hδn hExpn hsn v hv
  have hvnorm : ‖v‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hδnorm : ‖perturbation n (lam n) v‖ < 1 := by
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hδn v hv
  have hEnorm : ‖Complex.exp (v + perturbation n (lam n) v)‖ ≤ Real.exp ((1 / 4 : ℝ) + 1) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have ht := norm_add_le v (perturbation n (lam n) v)
    have hr := Complex.re_le_norm (v + perturbation n (lam n) v)
    linarith
  have hdiff : ‖Complex.exp (v + perturbation n (lam n) v) - Complex.exp v‖ < η / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hExpn v hv
  rw [A_exact (lt_of_lt_of_le Nat.zero_lt_one hnpos) hn]
  have halg : -(1 + v / lam n) * Complex.exp (v + perturbation n (lam n) v) + Complex.exp v =
      -(Complex.exp (v + perturbation n (lam n) v) - Complex.exp v) -
        (v / lam n) * Complex.exp (v + perturbation n (lam n) v) := by ring
  calc
    dist (-Complex.exp v) (-(1 + v / lam n) * Complex.exp (v + perturbation n (lam n) v)) =
        ‖-(1 + v / lam n) * Complex.exp (v + perturbation n (lam n) v) + Complex.exp v‖ := by
          rw [dist_eq_norm, norm_sub_rev, sub_neg_eq_add]
    _ ≤ ‖Complex.exp (v + perturbation n (lam n) v) - Complex.exp v‖ +
        (‖v‖ / ‖lam n‖) * ‖Complex.exp (v + perturbation n (lam n) v)‖ := by
      rw [halg]
      simpa only [norm_neg, norm_mul, norm_div] using norm_sub_le
        (-(Complex.exp (v + perturbation n (lam n) v) - Complex.exp v))
        ((v / lam n) * Complex.exp (v + perturbation n (lam n) v))
    _ ≤ ‖Complex.exp (v + perturbation n (lam n) v) - Complex.exp v‖ +
        Real.exp ((1 / 4 : ℝ) + 1) * ((1 / 4 : ℝ) / ‖lam n‖) := by
      have ht : (‖v‖ / ‖lam n‖) * ‖Complex.exp (v + perturbation n (lam n) v)‖ ≤
          Real.exp ((1 / 4 : ℝ) + 1) * ((1 / 4 : ℝ) / ‖lam n‖) := by
        calc
          _ ≤ ((1 / 4 : ℝ) / ‖lam n‖) * Real.exp ((1 / 4 : ℝ) + 1) := by gcongr
          _ = _ := by ring
      exact add_le_add_left ht _
    _ < η := by linarith

#print axioms uniform_perturbation
#print axioms uniform_A
end Transfer
end SquareFlowerCompletion
