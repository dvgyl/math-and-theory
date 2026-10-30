import GeneralVolterraCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology

noncomputable section
namespace GeneralNesterovExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {r : ℝ}

lemma momentReal_const (hr : 1 < r) (z : E) {t : ℝ} (ht : 0 ≤ t) :
    momentReal r (fun _ => z) t = (t ^ (r+1) / (r+1)) • z := by
  unfold momentReal
  rw [intervalIntegral.integral_smul_const]
  congr 1
  calc
    (∫ s in (0 : ℝ)..t, |s| ^ r) = ∫ s in (0 : ℝ)..t, s ^ r := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      simp only [abs_of_nonneg hs.1]
    _ = t ^ (r+1) / (r+1) := by
      rw [integral_rpow (Or.inl (by linarith : -1 < r)),
        Real.zero_rpow (by linarith : r+1 ≠ 0), sub_zero]

omit [CompleteSpace E] in
lemma momentReal_sub_const (hr : 1 < r) {f : ℝ → E} (hf : Continuous f)
    (z : E) (t : ℝ) :
    momentReal r (fun s => f s - z) t = momentReal r f t - momentReal r (fun _ => z) t := by
  unfold momentReal
  simp only [smul_sub]
  apply intervalIntegral.integral_sub
  · exact (((Real.continuous_rpow_const (by linarith : 0 ≤ r)).comp continuous_abs).smul hf).intervalIntegrable _ _
  · exact (((Real.continuous_rpow_const (by linarith : 0 ≤ r)).comp continuous_abs).smul continuous_const).intervalIntegrable _ _

lemma norm_velocity_ratio_error (hr : 1 < r) {f : ℝ → E} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ s, 0 ≤ s → ‖f s - f 0‖ ≤ B * s^2) {t : ℝ} (ht : 0 < t) :
    ‖t⁻¹ • velocity r f t + (r+1)⁻¹ • f 0‖ ≤ B * t^2 := by
  have hp : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  have hn : r+1 ≠ 0 := by linarith
  have hm : ‖momentReal r (fun s => f s - f 0) t‖ ≤ (B*t^2*t^r)*t := by
    have hbound : ∀ s ∈ uIoc (0 : ℝ) t, ‖|s|^r • (f s-f 0)‖ ≤ B*t^2*t^r := by
      intro s hs
      rw [uIoc_of_le ht.le] at hs
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_of_nonneg hs.1.le]
      have hpow : s^r ≤ t^r := Real.rpow_le_rpow hs.1.le hs.2 (by linarith)
      have hsq : s^2 ≤ t^2 := pow_le_pow_left₀ hs.1.le hs.2 2
      have hnorm := (hb s hs.1.le).trans (mul_le_mul_of_nonneg_left hsq hB)
      calc
        s^r * ‖f s-f 0‖ ≤ t^r * (B*t^2) := mul_le_mul hpow hnorm
          (norm_nonneg _) hp.le
        _ = B*t^2*t^r := by ring
    simpa only [momentReal, sub_zero, abs_of_pos ht] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hscalar : t⁻¹ * t^(-r) * (t^(r+1)/(r+1)) = (r+1)⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.rpow_add ht, Real.rpow_one]
    field_simp [ht.ne', hp.ne', hn]
    ring
  have hid : t⁻¹ • velocity r f t + (r+1)⁻¹ • f 0 =
      -(t⁻¹ * t^(-r)) • momentReal r (fun s => f s-f 0) t := by
    rw [momentReal_sub_const hr hf, momentReal_const hr (f 0) ht.le]
    simp only [velocity, abs_of_pos ht, smul_sub, smul_smul, neg_mul, mul_neg,
      neg_smul, smul_neg, neg_neg]
    rw [hscalar]
    module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht.le) (Real.rpow_nonneg ht.le _)),
    Real.rpow_neg ht.le]
  calc
    (t⁻¹ * (t^r)⁻¹) * ‖momentReal r (fun s => f s-f 0) t‖ ≤
        (t⁻¹ * (t^r)⁻¹) * ((B*t^2*t^r)*t) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = B*t^2 := by field_simp [ht.ne', hp.ne']; ring

def velocityRatio (r : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  if t = 0 then -(r+1)⁻¹ • f 0 else t⁻¹ • velocity r f t

omit [CompleteSpace E] in
@[simp] lemma velocityRatio_zero (f : ℝ → E) :
    velocityRatio r f 0 = -(r+1)⁻¹ • f 0 := by simp [velocityRatio]

lemma velocityRatio_continuousOn (hr : 1 < r) {f : ℝ → E} (hf : Continuous f)
    {B C : ℝ} (hB : 0 ≤ B)
    (hb : ∀ s, 0 ≤ s → ‖f s-f 0‖ ≤ B*s^2) (hc : ∀ s, ‖f s‖ ≤ C) :
    ContinuousOn (velocityRatio r f) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    change Tendsto (velocityRatio r f) (𝓝[Ici 0] 0) (𝓝 (velocityRatio r f 0))
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (g := fun t : ℝ => B*t^2) (Eventually.of_forall (fun _ => dist_nonneg))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 ≤ t at ht
      rcases ht.eq_or_lt with he | he
      · subst t; simp
      · simpa [dist_eq_norm, velocityRatio, he.ne', sub_eq_add_neg, neg_smul] using
          norm_velocity_ratio_error hr hf hB hb he
    · simpa using ((continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => B*t^2) (𝓝[Ici 0] (0 : ℝ)) (𝓝 (B*0^2)))
  · have hcont : ContinuousAt (fun t : ℝ => t⁻¹ • velocity r f t) t :=
      (continuousAt_id.inv₀ hpos.ne').smul (velocity_continuous hr hf hc).continuousAt
    have hcont' : ContinuousAt (velocityRatio r f) t := by
      apply hcont.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hpos] with s hs
      simp [velocityRatio, hs.ne']
    exact hcont'.continuousWithinAt

/-- The Volterra trajectory has a continuous acceleration on the closed time half-line.
The acceleration at the singular initial time is derived, not assumed. -/
theorem exists_global_nesterov_with_acceleration (hr : 1 < r) (g : E → E)
    (hg : LipschitzWith 1 g) (hb : ∀ x, ‖g x‖ ≤ 2) (q0 : E) :
    ∃ q u a : ℝ → E, Continuous q ∧ Continuous u ∧ ContinuousOn a (Ici 0) ∧
      q 0 = q0 ∧ u 0 = 0 ∧ a 0 = -(r+1)⁻¹ • g q0 ∧
      (∀ t, 0 ≤ t → HasDerivAt q (u t) t) ∧
      (∀ t, 0 < t → HasDerivAt u (a t) t) ∧
      (∀ t, 0 < t → a t = -(r/t) • u t - g (q t)) := by
  obtain ⟨q, hqc, hqn, hqi⟩ := exists_global_volterra hr g hg hb q0
  let f : ℝ → E := fun t => g (q t)
  have hfc : Continuous f := hg.continuous.comp hqc
  have hfb : ∀ t, ‖f t‖ ≤ 2 := fun t => hb _
  have hqid : ∀ t, 0 ≤ t → q t = q0 - (r-1)⁻¹ • momentOne f t +
      (t^(1-r)/(r-1)) • momentReal r f t := hqi
  have hqzero : q 0 = q0 := hqn 0 le_rfl
  have hdisp (t : ℝ) (ht : 0 ≤ t) : ‖q t-q0‖ ≤ 2*t^2 := by
    rcases ht.eq_or_lt with he | he
    · subst t; simp [hqzero]
    · have heq : q t-q0 = -volterra r f t := by
        rw [hqid t he.le, volterra_moments hr hfc]
        dsimp [momentOne, momentReal]
        abel
      rw [heq, norm_neg]
      exact volterra_norm_bound hr hfc (by norm_num) hfb he
  have hfdiff (t : ℝ) (ht : 0 ≤ t) : ‖f t-f 0‖ ≤ 2*t^2 := by
    have hl := hg.dist_le_mul (q t) (q 0)
    simp only [NNReal.coe_one, one_mul, dist_eq_norm, hqzero] at hl
    simpa only [f, hqzero] using hl.trans (hdisp t ht)
  let u := velocity r f
  let a : ℝ → E := fun t => -r • velocityRatio r f t - f t
  have hac : ContinuousOn a (Ici 0) :=
    (continuousOn_const.smul (velocityRatio_continuousOn hr hfc (by norm_num) hfdiff hfb)).sub hfc.continuousOn
  have haeq (t : ℝ) (ht : 0 < t) : a t = -(r/t) • u t - g (q t) := by
    dsimp [a, velocityRatio, u, f]
    rw [if_neg ht.ne', smul_smul]
    congr 2
    ring
  refine ⟨q, u, a, hqc, velocity_continuous hr hfc hfb, hac, hqzero,
    velocity_zero f, ?_, ?_, ?_, haeq⟩
  · dsimp [a]
    rw [velocityRatio_zero]
    change (-r) • ((-(r+1)⁻¹) • g (q 0)) - g (q 0) = -(r+1)⁻¹ • g q0
    rw [hqzero, smul_smul]
    have hs : -r * -(r+1)⁻¹ - 1 = -(r+1)⁻¹ := by
      field_simp [show r+1 ≠ 0 by linarith]
    calc
      (-r * -(r+1)⁻¹) • g q0 - g q0 = (-r * -(r+1)⁻¹ - 1) • g q0 := by
        rw [sub_smul, one_smul]
      _ = -(r+1)⁻¹ • g q0 := by rw [hs]
  · intro t ht
    rcases ht.eq_or_lt with he | he
    · subst t
      simpa only [u, velocity_zero] using
        volterra_hasDerivAt_zero hr hfc (by norm_num : (0:ℝ) ≤ 2) hfb hqid hqn
    · exact volterra_hasDerivAt_pos hr hfc hqid he
  · intro t ht
    rw [haeq t ht]
    exact velocity_hasDerivAt hr hfc ht

#print axioms exists_global_nesterov_with_acceleration
end GeneralNesterovExistence
