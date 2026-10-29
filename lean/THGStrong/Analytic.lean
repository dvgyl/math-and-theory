module
public import THGStrong.Core
public import THGStrong.AnalyticBase
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

noncomputable section
open scoped InnerProductSpace
namespace THGStrong

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma norm_sq_gradient (μ : ℝ) (x : E) :
    HasGradientAt (fun z : E => μ / 2 * ‖z‖ ^ 2) (μ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ / 2) using 1
  ext y
  simp only [smul_apply, InnerProductSpace.toDual_apply_apply,
    real_inner_smul_left, smul_eq_mul, innerSL_apply_apply]
  ring

lemma strong_first_order {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (x y : E) :
    f x + ⟪g x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hc := strongConvexOn_iff_convex.mp hf
  have hd (z : E) : HasGradientAt (fun t => f t - μ / 2 * ‖t‖ ^ 2) (g z - μ • z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hg z).hasFDerivAt.sub (norm_sq_gradient μ z).hasFDerivAt using 1
    simp only [map_sub]
  have hs := firstOrderSupport hc hd x y
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right] at hs
  rw [norm_sub_sq_real, real_inner_comm x y]
  simp only [inner_sub_right]
  rw [real_inner_self_eq_norm_sq] at hs
  nlinarith

lemma strong_interpolation_general {f : E → ℝ} {g : E → E} {μ L : ℝ}
    (hμ : μ < L) (hL : 0 < L)
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    0 ≤ 2 * (L - μ) * (f x - f y) -
      2 * ⟪L • g y - μ • g x, x - y⟫_ℝ - sq (g x - g y) - μ * L * sq (x - y) := by
  let d := (g x - g y) - μ • (x - y)
  let z := x - (L - μ)⁻¹ • d
  have hs := strong_first_order hf hg y z
  have hd := smoothDescent hg hL hLip x z
  have hc : 0 < L - μ := sub_pos.mpr hμ
  have he : 2 * (L - μ) * (f x - f y) -
      2 * ⟪L • g y - μ • g x, x - y⟫_ℝ - sq (g x - g y) - μ * L * sq (x - y) =
      2 * (L - μ) * (f x + ⟪g x, z - x⟫_ℝ + L / 2 * ‖z - x‖ ^ 2 -
        (f y + ⟪g y, z - y⟫_ℝ + μ / 2 * ‖z - y‖ ^ 2)) := by
    simp only [sq, z, d, ← real_inner_self_eq_norm_sq,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm x (g x), real_inner_comm x (g y),
      real_inner_comm y (g x), real_inner_comm y (g y),
      real_inner_comm y x, real_inner_comm (g y) (g x)]
    field_simp [ne_of_gt hc]
    ring
  rw [he]
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (le_trans hs hd))

lemma normalized_strong_interpolation {f : E → ℝ} {g : E → E} {μ L : ℝ}
    (hμ : μ < L) (hL : 0 < L)
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (xstar x y : E) :
    0 ≤ Q (μ / L) (x - xstar) (y - xstar) (L⁻¹ • g x) (L⁻¹ • g y)
      ((f x - f xstar) / L) ((f y - f xstar) / L) := by
  have ht := strong_interpolation_general hμ hL hf hg hLip x y
  have he : Q (μ / L) (x - xstar) (y - xstar) (L⁻¹ • g x) (L⁻¹ • g y)
      ((f x - f xstar) / L) ((f y - f xstar) / L) =
      (2 * (L - μ) * (f x - f y) -
        2 * ⟪L • g y - μ • g x, x - y⟫_ℝ - sq (g x - g y) - μ * L * sq (x - y)) / L ^ 2 := by
    have hd : (x - xstar) - (y - xstar) = x - y := by abel
    rw [Q, hd]
    simp only [sq, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    field_simp [ne_of_gt hL]
    ring
  rw [he]
  exact div_nonneg ht (by positivity)

#print axioms norm_sq_gradient
#print axioms strong_first_order
#print axioms strong_interpolation_general
#print axioms normalized_strong_interpolation

end THGStrong
