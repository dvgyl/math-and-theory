import GeneralVolterraOperator
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology

noncomputable section
namespace GeneralNesterovExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r : ℝ}

def momentOne (f : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, s • f s

def momentReal (r : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, |s| ^ r • f s

def velocity (r : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  -(|t| ^ (-r)) • momentReal r f t

lemma momentOne_hasDerivAt [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (momentOne f) (t • f t) t := by
  have hc : Continuous (fun s : ℝ => s • f s) := continuous_id.smul hf
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma momentReal_hasDerivAt (hr : 1 < r) [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (momentReal r f) (|t| ^ r • f t) t := by
  have hc : Continuous (fun s : ℝ => |s| ^ r • f s) :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ r)).comp continuous_abs).smul hf
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma norm_momentReal_le (hr : 1 < r) {f : ℝ → E} {B : ℝ}
    (hf : ∀ s, ‖f s‖ ≤ B) (t : ℝ) :
    ‖momentReal r f t‖ ≤ B * |t| ^ r * |t| := by
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖|s| ^ r • f s‖ ≤ B * |t| ^ r := by
    intro s hs
    have ha : |s| ≤ |t| := by
      simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hs)
    calc
      ‖|s| ^ r • f s‖ = |s| ^ r * ‖f s‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      _ ≤ |t| ^ r * B := mul_le_mul
        (Real.rpow_le_rpow (abs_nonneg _) ha (by linarith))
        (hf s) (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
      _ = B * |t| ^ r := mul_comm _ _
  simpa [momentReal, sub_zero, mul_assoc, mul_comm, mul_left_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

@[simp] lemma velocity_zero (f : ℝ → E) : velocity r f 0 = 0 := by
  simp [velocity, momentReal]

lemma norm_velocity_le (hr : 1 < r) {f : ℝ → E} {B : ℝ}
    (hf : ∀ s, ‖f s‖ ≤ B) (t : ℝ) : ‖velocity r f t‖ ≤ B * |t| := by
  by_cases ht : t = 0
  · simp [ht]
  · have hp : 0 < |t| ^ r := Real.rpow_pos_of_pos (abs_pos.mpr ht) _
    calc
      ‖velocity r f t‖ = (|t| ^ r)⁻¹ * ‖momentReal r f t‖ := by
        rw [velocity, norm_smul, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
          Real.rpow_neg (abs_nonneg _)]
      _ ≤ (|t| ^ r)⁻¹ * (B * |t| ^ r * |t|) :=
        mul_le_mul_of_nonneg_left (norm_momentReal_le hr hf t) (inv_nonneg.mpr hp.le)
      _ = B * |t| := by field_simp [hp.ne']; ring

lemma velocity_continuousAt_zero (hr : 1 < r) {f : ℝ → E} {B : ℝ}
    (hf : ∀ s, ‖f s‖ ≤ B) : ContinuousAt (velocity r f) 0 := by
  change Tendsto (velocity r f) (𝓝 0) (𝓝 (velocity r f 0))
  rw [velocity_zero]
  apply squeeze_zero_norm (norm_velocity_le hr hf)
  simpa using (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

lemma velocity_continuous (hr : 1 < r) [CompleteSpace E] {f : ℝ → E} {B : ℝ}
    (hfcont : Continuous f) (hf : ∀ s, ‖f s‖ ≤ B) : Continuous (velocity r f) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · simpa [ht] using velocity_continuousAt_zero hr hf
  · have hm := (momentReal_hasDerivAt hr hfcont t).continuousAt
    have hp : ContinuousAt (fun s : ℝ => |s| ^ (-r)) t :=
      (Real.continuousAt_rpow_const |t| (-r) (Or.inl (abs_ne_zero.mpr ht))).comp
        continuous_abs.continuousAt
    exact hp.neg.smul hm

lemma velocity_hasDerivAt (hr : 1 < r) [CompleteSpace E] {f : ℝ → E} (hf : Continuous f)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (velocity r f) (-(r / t) • velocity r f t - f t) t := by
  have hc : HasDerivAt (fun s : ℝ => -(s ^ (-r)))
      (r * t ^ (-r-1)) t := by
    convert (Real.hasDerivAt_rpow_const (p := -r) (Or.inl ht.ne')).neg using 1
    ring
  have h := hc.smul (momentReal_hasDerivAt hr hf t)
  have he : t ^ (-r) * t ^ r = 1 := by
    rw [← Real.rpow_add ht]
    simp
  have he2 : t ^ (-r-1) = t ^ (-r) / t := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  have hh : HasDerivAt (fun s : ℝ => -(s ^ (-r)) • momentReal r f s)
      (-(r / t) • velocity r f t - f t) t := by
    convert h using 1
    dsimp [velocity]
    rw [abs_of_pos ht]
    simp only [neg_smul, smul_smul, smul_neg, sub_eq_add_neg, he2]
    rw [show -r + -1 = -r-1 by ring, he2]
    simp only [neg_mul, he, neg_one_smul, neg_smul, neg_neg]
    module
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  simp only [velocity, abs_of_pos hs]

lemma volterra_hasDerivAt_pos (hr : 1 < r) [CompleteSpace E] {f q : ℝ → E} {q0 : E}
    (hf : Continuous f)
    (hq : ∀ t, 0 ≤ t → q t = q0 - (r-1)⁻¹ • momentOne f t +
      (t^(1-r)/(r-1)) • momentReal r f t)
    {t : ℝ} (ht : 0 < t) : HasDerivAt q (velocity r f t) t := by
  have hn : r-1 ≠ 0 := by linarith
  have hc : HasDerivAt (fun s : ℝ => s ^ (1-r) / (r-1)) (-(t ^ (-r))) t := by
    convert (Real.hasDerivAt_rpow_const (p := 1-r) (Or.inl ht.ne')).div_const (r-1) using 1
    rw [show 1-r-1 = -r by ring]
    field_simp [hn]
    ring
  have h := ((hasDerivAt_const t q0).sub
    ((momentOne_hasDerivAt hf t).const_smul (r-1)⁻¹)).add
    (hc.smul (momentReal_hasDerivAt hr hf t))
  have he : (t^(1-r)/(r-1)) * t^r = (r-1)⁻¹ * t := by
    have hc' := rpow_complement_mul ht r
    field_simp [hn]
    nlinarith
  have hh : HasDerivAt (fun s => q0 - (r-1)⁻¹ • momentOne f s +
      (s^(1-r)/(r-1)) • momentReal r f s) (velocity r f t) t := by
    convert h using 1
    dsimp [velocity]
    rw [abs_of_pos ht]
    simp only [zero_sub, smul_smul, he, neg_smul]
    module
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact hq s hs.le

lemma zero_derivative_of_quadratic_displacement {q : ℝ → E} {q0 : E} {B : ℝ}
    (_hB : 0 ≤ B) (hq0 : q 0 = q0)
    (hq : ∀ t, ‖q t - q0‖ ≤ B * |t| ^ 2) : HasDerivAt q 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero, smul_zero, sub_zero, hq0]
  apply squeeze_zero (g := fun t : ℝ => B * |t|)
    (fun t => mul_nonneg (inv_nonneg.mpr (norm_nonneg t)) (norm_nonneg _))
  · intro t
    by_cases ht : t = 0
    · simp [ht]
    · calc
        ‖t‖⁻¹ * ‖q t - q0‖ ≤ |t|⁻¹ * (B * |t| ^ 2) := by
          simpa only [Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left (hq t) (inv_nonneg.mpr (abs_nonneg t))
        _ = B * ((|t|⁻¹ * |t|) * |t|) := by ring
        _ = B * |t| := by rw [inv_mul_cancel₀ (abs_ne_zero.mpr ht), one_mul]
  · simpa using (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

lemma volterra_hasDerivAt_zero (hr : 1 < r) {f q : ℝ → E} {q0 : E} {B : ℝ}
    (hfcont : Continuous f) (hB : 0 ≤ B) (hf : ∀ s, ‖f s‖ ≤ B)
    (hq : ∀ t, 0 ≤ t → q t = q0 - (r-1)⁻¹ • momentOne f t +
      (t^(1-r)/(r-1)) • momentReal r f t)
    (hqneg : ∀ t, t ≤ 0 → q t = q0) : HasDerivAt q 0 0 := by
  apply zero_derivative_of_quadratic_displacement hB (hqneg 0 le_rfl)
  intro t
  by_cases ht : 0 < t
  · have he : q t - q0 = -volterra r f t := by
      rw [hq t ht.le, volterra_moments hr hfcont]
      dsimp [momentOne, momentReal]
      abel
    rw [he, norm_neg, sq_abs]
    exact volterra_norm_bound hr hfcont hB hf ht
  · rw [hqneg t (le_of_not_gt ht), sub_self, norm_zero]
    positivity

/-- A global weighted Volterra solution yields an actual classical Nesterov trajectory,
including the genuine two-sided derivative at zero of the constant-left extension. -/
theorem exists_global_nesterov (hr : 1 < r) [CompleteSpace E] (g : E → E)
    (hg : LipschitzWith 1 g) (hb : ∀ x, ‖g x‖ ≤ 2) (q0 : E) :
    ∃ q u : ℝ → E, Continuous q ∧ Continuous u ∧ q 0 = q0 ∧ u 0 = 0 ∧
      (∀ t, 0 ≤ t → HasDerivAt q (u t) t) ∧
      (∀ t, 0 < t → HasDerivAt u (-(r/t) • u t - g (q t)) t) := by
  obtain ⟨q, hqc, hqn, hqi⟩ := exists_global_volterra hr g hg hb q0
  let f : ℝ → E := fun t => g (q t)
  have hfc : Continuous f := hg.continuous.comp hqc
  have hfb : ∀ t, ‖f t‖ ≤ 2 := fun t => hb _
  have hqid : ∀ t, 0 ≤ t → q t = q0 - (r-1)⁻¹ • momentOne f t +
      (t^(1-r)/(r-1)) • momentReal r f t := hqi
  refine ⟨q, velocity r f, hqc, velocity_continuous hr hfc hfb,
    hqn 0 le_rfl, velocity_zero f, ?_, ?_⟩
  · intro t ht
    rcases ht.eq_or_lt with he | he
    · subst t
      simpa only [velocity_zero] using
        volterra_hasDerivAt_zero hr hfc (by norm_num : (0:ℝ) ≤ 2) hfb hqid hqn
    · exact volterra_hasDerivAt_pos hr hfc hqid he
  · intro t ht
    exact velocity_hasDerivAt hr hfc ht

#print axioms exists_global_nesterov
end GeneralNesterovExistence
