import NAGConjugacy
import HilbertModel

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DiscreteNesterov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def axisPotential (e : E) (F : ℝ → ℝ) (x : E) : ℝ := F ⟪e,x⟫_ℝ
def axisGradient (e : E) (G : ℝ → ℝ) (x : E) : E := G ⟪e,x⟫_ℝ • e

lemma axis_inner (e : E) (he : ‖e‖=1) (s : ℝ) : ⟪e,s • e⟫_ℝ=s := by
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  ring

lemma axisPotential_convex (e : E) {F : ℝ → ℝ} (hc : ConvexOn ℝ univ F) :
    ConvexOn ℝ univ (axisPotential e F) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa only [axisPotential, inner_add_right, inner_smul_right, smul_eq_mul] using
    hc.2 (mem_univ ⟪e,x⟫_ℝ) (mem_univ ⟪e,y⟫_ℝ) ha hb hab

lemma axisPotential_hasGradient (e : E) {F G : ℝ → ℝ}
    (hg : ∀ x, HasGradientAt F (G x) x) (x : E) :
    HasGradientAt (axisPotential e F) (axisGradient e G x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hg ⟪e,x⟫_ℝ).hasFDerivAt.comp x (innerSL ℝ e).hasFDerivAt
  convert hd using 1
  ext h
  simp only [axisGradient, toDual_apply, real_inner_smul_left,
    ContinuousLinearMap.comp_apply, innerSL_apply, RCLike.inner_apply, conj_trivial]
  ring

lemma axisGradient_lipschitz (e : E) (he : ‖e‖=1) {G : ℝ → ℝ}
    (hG : LipschitzWith 1 G) : LipschitzWith 1 (axisGradient e G) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hg := hG.dist_le_mul ⟪e,x⟫_ℝ ⟪e,y⟫_ℝ
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hg
  have hi : ‖⟪e,x⟫_ℝ-⟪e,y⟫_ℝ‖≤‖x-y‖ := by
    rw [← inner_sub_right]
    simpa only [he, one_mul] using norm_inner_le_norm e (x-y)
  calc
    ‖axisGradient e G x-axisGradient e G y‖=‖G ⟪e,x⟫_ℝ-G ⟪e,y⟫_ℝ‖ := by
      rw [axisGradient, axisGradient, ← sub_smul, norm_smul, he, mul_one]
    _≤‖⟪e,x⟫_ℝ-⟪e,y⟫_ℝ‖ := hg
    _≤‖x-y‖ := hi

lemma axisGradient_bound (e : E) (he : ‖e‖=1) {G : ℝ → ℝ}
    (hG : ∀ x, ‖G x‖≤2) (x : E) : ‖axisGradient e G x‖≤2 := by
  simpa only [axisGradient, norm_smul, he, mul_one] using hG ⟪e,x⟫_ℝ

/-- A scalar escaping sequence gives a genuine Hilbert-space escaping sequence
with the same fixed step and momentum parameters. -/
theorem lift_discrete_escape (e : E) (he : ‖e‖=1) {r b : ℝ} {G : ℝ → ℝ}
    (hescape : Tendsto (nagX r 1 G b) atTop atTop) :
    Tendsto (fun k => ‖nagX r 1 (axisGradient e G) (b • e) k‖) atTop atTop := by
  have hm (k : ℕ) : ⟪e,nagX r 1 (axisGradient e G) (b • e) k⟫_ℝ=nagX r 1 G b k := by
    have hc := (nag_map (innerSL ℝ e) r 1 1 (axisGradient e G) G (b • e)
      (fun x => by simp only [one_pow, one_smul, innerSL_apply, axisGradient, axis_inner e he]) k).1
    simpa only [innerSL_apply, axis_inner e he] using hc
  apply tendsto_atTop_mono _ hescape
  intro k
  rw [← hm k]
  have hi := real_inner_le_norm e (nagX r 1 (axisGradient e G) (b • e) k)
  simpa only [he, one_mul] using hi

open NesterovThresholdModel NesterovHilbert
def discreteUnitAxis : Hilbert := lp.single 2 0 (point 1 0)
lemma norm_discreteUnitAxis : ‖discreteUnitAxis‖=1 := by
  rw [discreteUnitAxis, lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
  have hs := norm_sq_eq (point 1 0)
  simp only [point_first, point_second, one_pow, zero_pow (by decide : 2≠0), add_zero] at hs
  nlinarith [norm_nonneg (point 1 0)]

end DiscreteNesterov
