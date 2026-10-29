import LambertCenter
import UniformInverse
import UniformSmallZero

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Lambert

def defect (L : ℝ) (v : ℂ) : ℂ :=
  (L : ℂ) + (Real.pi : ℂ) * Complex.I - Complex.log (center L + v) - center L - v

def defectDeriv (L : ℝ) (v : ℂ) : ℂ := -(center L + v)⁻¹ - 1

theorem defect_zero_tendsto (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => defect (L n) 0) atTop (𝓝 0) := by
  have h := (log_center_defect_tendsto_zero L hL).neg
  convert h using 1
  · funext n
    dsimp [defect, center]
    push_cast
    ring
  · simp

theorem uniform_defectDeriv (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    TendstoUniformlyOn (fun n v => defectDeriv (L n) v) (fun _ => -1) atTop
      (Metric.closedBall (0 : ℂ) 1) := by
  have h := uniform_inverse_shift (fun n => center (L n)) 1 (center_re_tendsto_atTop L hL)
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 h) ε hε] with n hn v hv
  have heq : (-1 : ℂ) - defectDeriv (L n) v = (center (L n) + v)⁻¹ := by
    dsimp [defectDeriv]; ring
  simpa only [dist_eq_norm, zero_sub, norm_neg, heq] using hn v hv

theorem eventually_hasDerivAt_defect (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    ∀ᶠ n in atTop, ∀ v ∈ Metric.closedBall (0 : ℂ) 1,
      HasDerivAt (defect (L n)) (defectDeriv (L n) v) v := by
  filter_upwards [(center_re_tendsto_atTop L hL).eventually_gt_atTop 2] with n hn v hv
  have hvnorm : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hvre : -1 ≤ v.re := by
    have h := Complex.abs_re_le_norm v
    linarith [neg_abs_le v.re]
  have hs : center (L n) + v ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.2
    left
    simp only [Complex.add_re]
    linarith
  have hc : HasDerivAt (fun z : ℂ => center (L n) + z) 1 v := by
    simpa using (hasDerivAt_const v (center (L n))).add (hasDerivAt_id v)
  have hl := (Complex.hasDerivAt_log hs).comp v hc
  have h := (((hasDerivAt_const v ((L n : ℂ) + (Real.pi : ℂ) * Complex.I)).sub hl).sub
    (hasDerivAt_const v (center (L n)))).sub (hasDerivAt_id v)
  simpa [defect, defectDeriv] using h

/-- An actual principal-log Lambert solution with the full additive asymptotic.
All eventual slit-plane and nonzero conditions are proved in the construction. -/
theorem exists_lambert_sequence (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    ∃ lam : ℕ → ℂ,
      Tendsto (fun n => lam n - center (L n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, lam n ∈ Complex.slitPlane ∧
        lam n + Complex.log (lam n) = (L n : ℂ) + (Real.pi : ℂ) * Complex.I ∧
        lam n * Complex.exp (lam n) = -Complex.exp (L n : ℂ) := by
  obtain ⟨v, hvlim, hvroot⟩ := exists_zero_sequence_of_uniform_derivative
    (fun n => defect (L n)) (fun n => defectDeriv (L n)) (fun _ => -1) 1 (by norm_num)
    (defect_zero_tendsto L hL) (eventually_hasDerivAt_defect L hL)
    (uniform_defectDeriv L hL) (by intro z hz; norm_num)
  refine ⟨fun n => center (L n) + v n, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using hvlim
  · filter_upwards [hvroot, (center_re_tendsto_atTop L hL).eventually_gt_atTop 2] with n hn hc
    have hvnorm : ‖v n‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hn.1
    have hvre : -1 ≤ (v n).re := by
      have h := Complex.abs_re_le_norm (v n)
      linarith [neg_abs_le (v n).re]
    have hs : center (L n) + v n ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.2
      left
      simp only [Complex.add_re]
      linarith
    have heq : center (L n) + v n + Complex.log (center (L n) + v n) =
        (L n : ℂ) + (Real.pi : ℂ) * Complex.I := by
      have h := hn.2.1
      dsimp [defect] at h
      linear_combination -h
    refine ⟨hs, heq, ?_⟩
    have h := congrArg Complex.exp heq
    simp only [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero hs),
      Complex.exp_pi_mul_I, mul_neg_one] at h
    simpa only [Complex.exp_add, mul_comm] using h

#print axioms exists_lambert_sequence
end Lambert
end SquareFlowerCompletion
