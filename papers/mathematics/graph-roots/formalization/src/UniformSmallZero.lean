import SmallZero
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section
open Filter Topology

namespace SquareFlowerCompletion

/-- Uniform derivative control and a vanishing initial defect give a shrinking family
of true zeros. The hypotheses remain explicit; no graph or root asymptotic is assumed. -/
theorem exists_zero_sequence_of_uniform_derivative
    (H d : ℕ → ℂ → ℂ) (dlim : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hzero : Tendsto (fun n => H n 0) atTop (𝓝 0))
    (hderiv : ∀ᶠ n in atTop, ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      HasDerivAt (H n) (d n z) z)
    (hunif : TendstoUniformlyOn d dlim atTop (Metric.closedBall (0 : ℂ) r))
    (hlimit : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖1 + dlim z‖ ≤ (1 / 3 : ℝ)) :
    ∃ z : ℕ → ℂ, Tendsto z atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, z n ∈ Metric.closedBall (0 : ℂ) r ∧
        H n (z n) = 0 ∧ ‖z n‖ ≤ 2 * ‖H n 0‖ := by
  classical
  have hnorm : Tendsto (fun n => ‖H n 0‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hzero.norm
  have hsmall : ∀ᶠ n in atTop, ‖H n 0‖ ≤ r / 2 :=
    (hnorm.eventually (gt_mem_nhds (half_pos hr))).mono fun n hn => hn.le
  have hclose := (Metric.tendstoUniformlyOn_iff.1 hunif) (1 / 6) (by norm_num)
  have hexists : ∀ᶠ n in atTop, ∃ z ∈ Metric.closedBall (0 : ℂ) r,
      H n z = 0 ∧ ‖z‖ ≤ 2 * ‖H n 0‖ := by
    filter_upwards [hsmall, hderiv, hclose] with n hs hd hc
    apply exists_small_zero_of_derivative (H n) (d n) r hr hs hd
    intro z hz
    have he : ‖d n z - dlim z‖ < (1 / 6 : ℝ) := by
      simpa only [dist_eq_norm, norm_sub_rev] using hc z hz
    calc
      ‖1 + d n z‖ = ‖(1 + dlim z) + (d n z - dlim z)‖ := by congr 1; ring
      _ ≤ ‖1 + dlim z‖ + ‖d n z - dlim z‖ := norm_add_le _ _
      _ ≤ (1 / 2 : ℝ) := by linarith [hlimit z hz]
  let z : ℕ → ℂ := fun n => if h : ∃ w ∈ Metric.closedBall (0 : ℂ) r,
      H n w = 0 ∧ ‖w‖ ≤ 2 * ‖H n 0‖ then Classical.choose h else 0
  have hz : ∀ᶠ n in atTop, z n ∈ Metric.closedBall (0 : ℂ) r ∧
      H n (z n) = 0 ∧ ‖z n‖ ≤ 2 * ‖H n 0‖ := by
    filter_upwards [hexists] with n hn
    dsimp only [z]
    rw [dif_pos hn]
    exact Classical.choose_spec hn
  refine ⟨z, ?_, hz⟩
  apply squeeze_zero_norm' (hz.mono fun n hn => hn.2.2)
  simpa only [mul_zero] using (tendsto_const_nhds.mul hnorm :
    Tendsto (fun n => (2 : ℝ) * ‖H n 0‖) atTop (𝓝 (2 * 0)))

#print axioms exists_zero_sequence_of_uniform_derivative

end SquareFlowerCompletion
