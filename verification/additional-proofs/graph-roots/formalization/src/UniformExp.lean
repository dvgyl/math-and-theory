import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion

theorem norm_exp_add_sub_exp_le {z h : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (hh : ‖h‖ ≤ 1) :
    ‖Complex.exp (z + h) - Complex.exp z‖ ≤ Real.exp (r + 1) * ‖h‖ := by
  have hd : ∀ x ∈ Metric.closedBall (0 : ℂ) (r + 1),
      HasDerivWithinAt Complex.exp (Complex.exp x) (Metric.closedBall (0 : ℂ) (r + 1)) x := by
    intro x hx
    exact (Complex.hasDerivAt_exp x).hasDerivWithinAt
  have hb : ∀ x ∈ Metric.closedBall (0 : ℂ) (r + 1), ‖Complex.exp x‖ ≤ Real.exp (r + 1) := by
    intro x hx
    have hxnorm : ‖x‖ ≤ r + 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm x).trans hxnorm)
  have hzball : z ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hzplus : z + h ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    have ht := norm_add_le z h
    linarith
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := z) (y := z + h) hd hb (convex_closedBall (0 : ℂ) (r + 1)) hzball hzplus
  simpa only [add_sub_cancel_left] using hbound

/-- Exponentiation preserves a vanishing uniform perturbation on a fixed disk. -/
theorem uniform_exp_add (δ : ℕ → ℂ → ℂ) (r : ℝ)
    (hδ : TendstoUniformlyOn δ (fun _ => 0) atTop (Metric.closedBall (0 : ℂ) r)) :
    TendstoUniformlyOn (fun n v => Complex.exp (v + δ n v)) Complex.exp atTop
      (Metric.closedBall (0 : ℂ) r) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  have hC : 0 < Real.exp (r + 1) := Real.exp_pos _
  have htol : 0 < min (1 : ℝ) (η / Real.exp (r + 1)) := lt_min (by norm_num) (div_pos hη hC)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hδ) _ htol] with n hn v hv
  have hvnorm : ‖v‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hd : ‖δ n v‖ < min (1 : ℝ) (η / Real.exp (r + 1)) := by
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hn v hv
  have hd1 : ‖δ n v‖ ≤ 1 := (hd.trans_le (min_le_left _ _)).le
  have hdη : ‖δ n v‖ < η / Real.exp (r + 1) := hd.trans_le (min_le_right _ _)
  calc
    dist (Complex.exp v) (Complex.exp (v + δ n v)) =
        ‖Complex.exp (v + δ n v) - Complex.exp v‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ Real.exp (r + 1) * ‖δ n v‖ := norm_exp_add_sub_exp_le hvnorm hd1
    _ < η := by nlinarith [(lt_div_iff₀ hC).mp hdη]

#print axioms uniform_exp_add
end SquareFlowerCompletion
