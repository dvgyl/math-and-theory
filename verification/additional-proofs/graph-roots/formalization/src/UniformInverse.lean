import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion

/-- Inversion vanishes uniformly on any fixed translated disk whose center's
real part tends to positive infinity. -/
theorem uniform_inverse_shift (c : ℕ → ℂ) (r : ℝ)
    (hc : Tendsto (fun n => (c n).re) atTop atTop) :
    TendstoUniformlyOn (fun (n : ℕ) v => (c n + v)⁻¹)
      (fun _ => 0) atTop (Metric.closedBall (0 : ℂ) r) := by
  have ha : Tendsto (fun n => (c n).re - r) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-r) hc
  have hi : Tendsto (fun n => ((c n).re - r)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ha
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  filter_upwards [ha.eventually_gt_atTop 0, hi.eventually (gt_mem_nhds hε)] with n hn he v hv
  have hvnorm : ‖v‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hvre : -‖v‖ ≤ v.re := by
    have h := Complex.abs_re_le_norm v
    linarith [neg_abs_le v.re]
  have hlow : (c n).re - r ≤ ‖c n + v‖ := by
    have h := Complex.re_le_norm (c n + v)
    simp only [Complex.add_re] at h
    linarith
  calc
    dist 0 (c n + v)⁻¹ = 1 / ‖c n + v‖ := by simp only [dist_eq_norm, zero_sub, norm_neg, norm_inv, one_div]
    _ ≤ 1 / ((c n).re - r) := one_div_le_one_div_of_le hn hlow
    _ < ε := by simpa only [one_div] using he

#print axioms uniform_inverse_shift
end SquareFlowerCompletion
