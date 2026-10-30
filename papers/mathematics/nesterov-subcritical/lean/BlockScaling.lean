import HilbertSum
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option linter.unusedSectionVars false
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal

namespace NesterovHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scalePotential (a ε : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  a^2*ε^2*f (a⁻¹ • x)

def scaleGradient (a ε : ℝ) (g : E → E) (x : E) : E :=
  (a*ε^2) • g (a⁻¹ • x)

lemma scale_hasGradient {a ε : ℝ} (ha : 0<a) {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasGradientAt f (g x) x) (x : E) :
    HasGradientAt (scalePotential a ε f) (scaleGradient a ε g x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := ((hf (a⁻¹ • x)).hasFDerivAt.comp x
    ((a⁻¹ • ContinuousLinearMap.id ℝ E).hasFDerivAt)).const_mul (a^2*ε^2)
  convert hd using 1
  ext h
  simp only [scaleGradient, toDual_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    real_inner_smul_left, real_inner_smul_right]
  field_simp
  ring

lemma scale_convex {a ε : ℝ} {f : E → ℝ} (hc : ConvexOn ℝ univ f) :
    ConvexOn ℝ univ (scalePotential a ε f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ b c hb hc' hbc
  have h := mul_le_mul_of_nonneg_left
    (hc.2 (mem_univ (a⁻¹ • x)) (mem_univ (a⁻¹ • y)) hb hc' hbc)
    (mul_nonneg (sq_nonneg a) (sq_nonneg ε))
  simpa only [scalePotential, smul_add, smul_smul, mul_comm a⁻¹ b, mul_comm a⁻¹ c,
    smul_eq_mul, mul_add, mul_left_comm] using h

lemma scale_nonneg {a ε : ℝ} {f : E → ℝ} (hf : ∀ x, 0≤f x) (x : E) :
    0≤scalePotential a ε f x := by
  exact mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg ε)) (hf _)

lemma scale_zero {a ε : ℝ} {f : E → ℝ} (hf : f 0=0) :
    scalePotential a ε f 0=0 := by simp [scalePotential, hf]

lemma scale_bound {a ε : ℝ} (ha : 0<a) (he0 : 0≤ε) (he1 : ε≤1)
    {g : E → E} (hg : ∀ x, ‖g x‖≤3) (x : E) :
    ‖scaleGradient a ε g x‖≤3*a := by
  have he2 : ε^2≤1 := by nlinarith
  have hg0 := norm_nonneg (g (a⁻¹ • x))
  have h := mul_le_mul_of_nonneg_left (hg (a⁻¹ • x))
    (mul_nonneg ha.le (sq_nonneg ε))
  rw [scaleGradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left he2 ha.le]

lemma scale_lipschitz {a ε : ℝ} (ha : 0<a) (he : 0<ε) (he1 : ε≤1)
    {g : E → E} (hg : ∀ x y, ‖g x-g y‖≤ε⁻¹*‖x-y‖) :
    LipschitzWith 1 (scaleGradient a ε g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h := mul_le_mul_of_nonneg_left (hg (a⁻¹ • x) (a⁻¹ • y))
    (mul_nonneg ha.le (sq_nonneg ε))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)] at h
  have heq : a*ε^2*(ε⁻¹*(a⁻¹*‖x-y‖))=ε*‖x-y‖ := by field_simp; ring
  rw [heq] at h
  rw [scaleGradient, scaleGradient, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact h.trans (by nlinarith [norm_nonneg (x-y)])

def weight (n : ℕ) : ℝ := ((1:ℝ)/2)^n/16

lemma weight_pos (n : ℕ) : 0<weight n := by unfold weight; positivity
lemma weight_le_one (n : ℕ) : weight n≤1 := by
  have h := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2≤1) (n := n)
  unfold weight
  linarith
lemma weight_summable : Summable weight := summable_geometric_two.div_const 16
lemma weight_sum : ∑' n, weight n=1/8 := by
  change (∑' n : ℕ, ((1:ℝ)/2)^n/16)=1/8
  rw [tsum_div_const, tsum_geometric_two]
  norm_num
lemma weight_bound_summable : Summable (fun n => 3*weight n) := weight_summable.mul_left 3
lemma weight_bound_sum : ∑' n, 3*weight n=3/8 := by rw [tsum_mul_left, weight_sum]; norm_num

def initialData (b : E) : SumSpace E := sumGradient (fun n _ => weight n • b) 0

lemma initialData_apply (b : E) (n : ℕ) : initialData b n=weight n • b := by
  apply sumGradient_apply (weight_summable.mul_right ‖b‖)
  intro n x
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos n)]

end NesterovHilbert
