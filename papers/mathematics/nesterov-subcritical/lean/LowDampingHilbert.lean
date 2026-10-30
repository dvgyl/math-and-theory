import HilbertModel
import LowDampingMain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal

namespace NesterovAxisLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def potential (e : E) (F : ℝ → ℝ) (x : E) : ℝ := F ⟪e, x⟫_ℝ
def gradient (e : E) (G : ℝ → ℝ) (x : E) : E := G ⟪e, x⟫_ℝ • e

lemma inner_axis (e : E) (he : ‖e‖ = 1) (s : ℝ) : ⟪e, s • e⟫_ℝ = s := by
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  ring

lemma potential_convex (e : E) {F : ℝ → ℝ} (hF : ConvexOn ℝ univ F) :
    ConvexOn ℝ univ (potential e F) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa only [potential, inner_add_right, inner_smul_right, smul_eq_mul] using
    hF.2 (mem_univ ⟪e, x⟫_ℝ) (mem_univ ⟪e, y⟫_ℝ) ha hb hab

lemma potential_hasGradient (e : E) {F G : ℝ → ℝ}
    (hF : ∀ x, HasGradientAt F (G x) x) (x : E) :
    HasGradientAt (potential e F) (gradient e G x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hF ⟪e, x⟫_ℝ).hasFDerivAt.comp x (innerSL ℝ e).hasFDerivAt
  convert hd using 1
  ext h
  simp only [gradient, toDual_apply, real_inner_smul_left,
    ContinuousLinearMap.comp_apply, innerSL_apply, RCLike.inner_apply, conj_trivial]
  ring

lemma gradient_lipschitz (e : E) (he : ‖e‖ = 1) {G : ℝ → ℝ}
    (hG : LipschitzWith 1 G) : LipschitzWith 1 (gradient e G) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hg := hG.dist_le_mul ⟪e, x⟫_ℝ ⟪e, y⟫_ℝ
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hg
  have hi : ‖⟪e, x⟫_ℝ - ⟪e, y⟫_ℝ‖ ≤ ‖x - y‖ := by
    rw [← inner_sub_right]
    simpa only [he, one_mul] using norm_inner_le_norm e (x - y)
  calc
    ‖gradient e G x - gradient e G y‖ = ‖G ⟪e, x⟫_ℝ - G ⟪e, y⟫_ℝ‖ := by
      rw [gradient, gradient, ← sub_smul, norm_smul, he, mul_one]
    _ ≤ ‖⟪e, x⟫_ℝ - ⟪e, y⟫_ℝ‖ := hg
    _ ≤ ‖x - y‖ := hi

lemma gradient_bound (e : E) (he : ‖e‖ = 1) {G : ℝ → ℝ}
    (hG : ∀ x, ‖G x‖ ≤ 2) (x : E) : ‖gradient e G x‖ ≤ 2 := by
  simpa only [gradient, norm_smul, he, mul_one] using hG ⟪e, x⟫_ℝ

/-- A one-dimensional actual gradient flow embeds along any unit axis without
changing damping, smoothness, minimum attainment, or zero initial velocity. -/
theorem lift_flow (e : E) (he : ‖e‖ = 1) {r : ℝ} {F G X V : ℝ → ℝ} {z : ℝ}
    (hconv : ConvexOn ℝ univ F) (hgrad : ∀ x, HasGradientAt F (G x) x)
    (hLip : LipschitzWith 1 G) (hbound : ∀ x, ‖G x‖ ≤ 2)
    (hFz : F z = 0) (hFpos : ∀ x, 0 ≤ F x)
    (hX : Continuous X) (hV : Continuous V) (hX0 : X 0 = 0) (hV0 : V 0 = 0)
    (hXd : ∀ t ≥ 0, HasDerivAt X (V t) t)
    (hVd : ∀ t > 0, HasDerivAt V (-(r / t) * V t - G (X t)) t)
    (hescape : Tendsto X atTop atTop) :
    ConvexOn ℝ univ (potential e F) ∧
      (∀ x, HasGradientAt (potential e F) (gradient e G x) x) ∧
      LipschitzWith 1 (gradient e G) ∧ (∀ x, ‖gradient e G x‖ ≤ 2) ∧
      potential e F (z • e) = 0 ∧ (∀ x, 0 ≤ potential e F x) ∧
      Continuous (fun t => X t • e) ∧ Continuous (fun t => V t • e) ∧
      X 0 • e = 0 ∧ V 0 • e = 0 ∧
      (∀ t ≥ 0, HasDerivAt (fun s => X s • e) (V t • e) t) ∧
      (∀ t > 0, HasDerivAt (fun s => V s • e)
        (-(r / t) • (V t • e) - gradient e G (X t • e)) t) ∧
      Tendsto (fun t => ‖X t • e‖) atTop atTop := by
  refine ⟨potential_convex e hconv, potential_hasGradient e hgrad,
    gradient_lipschitz e he hLip, gradient_bound e he hbound,
    ?_, fun x => hFpos _, hX.smul continuous_const, hV.smul continuous_const,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [potential, inner_axis e he] using hFz
  · rw [hX0, zero_smul]
  · rw [hV0, zero_smul]
  · intro t ht
    exact (hXd t ht).smul_const e
  · intro t ht
    convert (hVd t ht).smul_const e using 1
    simp only [gradient, inner_axis e he, sub_smul, mul_smul]
  · apply tendsto_atTop_mono _ hescape
    intro t
    rw [norm_smul, he, mul_one, Real.norm_eq_abs]
    exact le_abs_self (X t)

end NesterovAxisLift

namespace NesterovSharpThreshold
open NesterovThresholdModel NesterovHilbert

def unitAxis : Hilbert := lp.single 2 0 (point 1 0)

lemma norm_unitAxis : ‖unitAxis‖ = 1 := by
  rw [unitAxis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  have hs := norm_sq_eq (point 1 0)
  simp only [point_first, point_second, one_pow, zero_pow (by decide : 2 ≠ 0), add_zero] at hs
  nlinarith [norm_nonneg (point 1 0)]

/-- The classical low-damping example lifted to the same concrete Hilbert space
as the new subcritical construction. This is a completion of the range, not
an additional novelty claim. -/
theorem exists_low_damping_norm_divergent_flow {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (F : Hilbert → ℝ) (G : Hilbert → Hilbert) (X V : ℝ → Hilbert) (z : Hilbert),
      ConvexOn ℝ univ F ∧
      (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧ (∀ x, ‖G x‖ ≤ 2) ∧
      F z = 0 ∧ (∀ x, 0 ≤ F x) ∧
      Continuous X ∧ Continuous V ∧ X 0 = 0 ∧ V 0 = 0 ∧
      (∀ t ≥ 0, HasDerivAt X (V t) t) ∧
      (∀ t > 0, HasDerivAt V (-(r / t) • V t - G (X t)) t) ∧
      Tendsto (fun t => ‖X t‖) atTop atTop := by
  obtain ⟨F, G, X, V, z, hconv, hgrad, hLip, hbound, hFz, hFpos,
    hX, hV, hX0, hV0, hXd, hVd, hescape⟩ :=
    NesterovLowDamping.exists_low_damping_escape hr hr1
  exact ⟨NesterovAxisLift.potential unitAxis F, NesterovAxisLift.gradient unitAxis G,
    (fun t => X t • unitAxis), (fun t => V t • unitAxis), z • unitAxis,
    NesterovAxisLift.lift_flow unitAxis norm_unitAxis hconv hgrad hLip hbound hFz hFpos
      hX hV hX0 hV0 hXd hVd hescape⟩

#print axioms exists_low_damping_norm_divergent_flow

end NesterovSharpThreshold
