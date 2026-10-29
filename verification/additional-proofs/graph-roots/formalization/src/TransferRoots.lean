import DerivativeLimitA
import DerivativeLimitB
import TransferLimitB
import UniformSmallZero

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

def HD (n : ℕ) (lam v : ℂ) : ℂ := AD n lam v - BD n lam v

theorem eventually_hasDerivAt_H (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    ∀ᶠ (n : ℕ) in atTop, ∀ v ∈ Metric.closedBall (0 : ℂ) (1 / 4),
      HasDerivAt (H n (lam n)) (HD n (lam n) v) v := by
  have hnorm := lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd
  have hε := epsilon_tendsto_zero logScale lam logScale_tendsto_atTop hd
  filter_upwards [he, eventually_ge_atTop 1, hnorm.eventually_gt_atTop (1 / 4),
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))] with n hn hnp hnl hεn v hv
  have hvnorm : ‖v‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hw : ‖reciprocalCoordinate (lam n) v‖ ≤ (1 / 16 : ℝ) :=
    (reciprocalCoordinate_bound _ _ hvnorm).trans hεn.le
  have hv0 : lam n + v ≠ 0 := by
    intro hz
    have h := norm_sub_norm_le (lam n) (-v)
    rw [norm_neg, sub_neg_eq_add, hz, norm_zero] at h
    linarith
  have hA := hasDerivAt_A (lt_of_lt_of_le Nat.zero_lt_one hnp) hn hv0 hw
  have hB := hasDerivAt_B (n := n) hw
  simpa only [H, HD, AD, zero_add] using ((hasDerivAt_const v (1 : ℂ)).add hA).sub hB

theorem uniform_HD (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    TendstoUniformlyOn (fun n v => HD n (lam n) v) (fun v => -Complex.exp v) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have h := (uniform_AD lam hd he).sub (uniform_BD lam hd)
  change TendstoUniformlyOn (fun n v => HD n (lam n) v)
    (fun v => -Complex.exp v - 0) atTop (Metric.closedBall (0 : ℂ) (1 / 4)) at h
  simpa only [sub_zero] using h

theorem limit_derivative_bound {v : ℂ} (hv : ‖v‖ ≤ (1 / 4 : ℝ)) :
    ‖1 + -Complex.exp v‖ ≤ (1 / 3 : ℝ) := by
  have ht := Complex.norm_exp_sub_one_sub_id_le (by linarith : ‖v‖ ≤ 1)
  have htri := norm_add_le (Complex.exp v - 1 - v) v
  rw [sub_add_cancel] at htri
  have hs : ‖v‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by gcongr
  rw [← sub_eq_add_neg, norm_sub_rev]
  nlinarith

/-- Actual zeros of the full reciprocal function, with shrinking coordinate errors. -/
theorem exists_perturbed_zeros (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    ∃ v : ℕ → ℂ, Tendsto v atTop (𝓝 0) ∧
      ∀ᶠ (n : ℕ) in atTop, v n ∈ Metric.closedBall (0 : ℂ) (1 / 4) ∧
        H n (lam n) (v n) = 0 ∧ ‖v n‖ ≤ 2 * ‖H n (lam n) 0‖ := by
  have h0 : Tendsto (fun n => H n (lam n) 0) atTop (𝓝 0) := by
    simpa only [Complex.exp_zero, sub_self] using (uniform_H lam hd he).tendsto_at (x := (0 : ℂ)) (by simp)
  apply exists_zero_sequence_of_uniform_derivative
    (fun n => H n (lam n)) (fun n => HD n (lam n)) (fun v => -Complex.exp v)
    (1 / 4) (by norm_num) h0 (eventually_hasDerivAt_H lam hd he) (uniform_HD lam hd he)
  intro v hv
  exact limit_derivative_bound (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)

#print axioms eventually_hasDerivAt_H
#print axioms uniform_HD
#print axioms exists_perturbed_zeros
end Transfer
end SquareFlowerCompletion
