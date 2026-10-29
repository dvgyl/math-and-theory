import TransferLimitA

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

theorem norm_B_le {n : ℕ} {lam v : ℂ}
    (hw : ‖reciprocalCoordinate lam v‖ ≤ (1 / 16 : ℝ)) :
    ‖B n lam v‖ ≤ (1 / 128 : ℝ) ^ n := by
  obtain ⟨hps, hqs⟩ := slitPlane_bounds hw
  obtain ⟨hp, hq⟩ := denominator_bounds hw
  rw [B_eq_rational (Complex.slitPlane_ne_zero hps), norm_div, norm_pow, norm_pow]
  calc
    ‖reciprocalCoordinate lam v‖ ^ (2 * n + 1) / ‖P (reciprocalCoordinate lam v)‖ ^ n ≤
        (1 / 16 : ℝ) ^ (2 * n + 1) / (1 / 2 : ℝ) ^ n := by gcongr
    _ = (1 / 16 : ℝ) * (((1 / 16 : ℝ) ^ 2) ^ n / (1 / 2 : ℝ) ^ n) := by
      rw [pow_add, pow_one, pow_mul]
      ring
    _ = (1 / 16 : ℝ) * (1 / 128 : ℝ) ^ n := by
      rw [← div_pow]
      norm_num
    _ ≤ (1 / 128 : ℝ) ^ n := by
      have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 128) n
      nlinarith

theorem uniform_B (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n v => B n (lam n) v) (fun _ => 0) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have hε := epsilon_tendsto_zero logScale lam logScale_tendsto_atTop hd
  have hpow : Tendsto (fun n : ℕ => (1 / 128 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  filter_upwards [hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hpow.eventually (gt_mem_nhds hη)] with n hεn hn v hv
  have hvnorm : ‖v‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hw : ‖reciprocalCoordinate (lam n) v‖ ≤ (1 / 16 : ℝ) :=
    (reciprocalCoordinate_bound _ _ hvnorm).trans hεn.le
  simpa only [dist_eq_norm, zero_sub, norm_neg] using (norm_B_le hw).trans_lt hn

theorem uniform_H (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    TendstoUniformlyOn (fun n v => H n (lam n) v) (fun v => 1 - Complex.exp v) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have h1 : TendstoUniformlyOn (fun (_ : ℕ) (_ : ℂ) => (1 : ℂ)) (fun _ => 1) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).tendstoUniformlyOn_const _
  have ht := (h1.add (uniform_A lam hd he)).sub (uniform_B lam hd)
  change TendstoUniformlyOn (fun n v => H n (lam n) v)
    (fun v => (1 : ℂ) + -Complex.exp v - 0) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) at ht
  simpa only [sub_zero, ← sub_eq_add_neg] using ht

#print axioms norm_B_le
#print axioms uniform_B
#print axioms uniform_H
end Transfer
end SquareFlowerCompletion
