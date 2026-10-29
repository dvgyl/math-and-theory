import ReciprocalLog
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Reciprocal

/-- The literal reciprocal logarithm has uniformly vanishing scaled error on any
parameter set when its coordinate bound satisfies the required cubic scale. -/
theorem uniform_scaled_log_remainder
    {S : Set ℂ} (w : ℕ → ℂ → ℂ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hscale : Tendsto (fun n : ℕ => (n : ℝ) * ε n ^ 3) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ v ∈ S, ‖w n v‖ ≤ ε n) :
    TendstoUniformlyOn
      (fun (n : ℕ) v => (n : ℂ) * (Complex.log (Q (w n v)) -
        Complex.log (P (w n v)) + 2 * (w n v) ^ 2))
      (fun _ => 0) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  have hsmall : ∀ᶠ n in atTop, ε n < (1 / 16 : ℝ) :=
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hscaled : Tendsto (fun n : ℕ => 100 * ((n : ℝ) * ε n ^ 3)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hscale :
      Tendsto (fun n : ℕ => (100 : ℝ) * ((n : ℝ) * ε n ^ 3)) atTop (𝓝 (100 * 0)))
  filter_upwards [hsmall, hbound, hscaled.eventually (gt_mem_nhds hη)] with n hs hb ht v hv
  have hw := hb v hv
  have hr := norm_log_remainder_le (hw.trans hs.le)
  calc
    dist 0 ((n : ℂ) * (Complex.log (Q (w n v)) -
        Complex.log (P (w n v)) + 2 * (w n v) ^ 2)) =
        (n : ℝ) * ‖Complex.log (Q (w n v)) -
          Complex.log (P (w n v)) + 2 * (w n v) ^ 2‖ := by
            simp [dist_eq_norm, norm_mul]
    _ ≤ (n : ℝ) * (100 * ‖w n v‖ ^ 3) :=
      mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n)
    _ ≤ (n : ℝ) * (100 * ε n ^ 3) := by gcongr
    _ = 100 * ((n : ℝ) * ε n ^ 3) := by ring
    _ < η := ht

#print axioms uniform_scaled_log_remainder
end Reciprocal
end SquareFlowerCompletion
