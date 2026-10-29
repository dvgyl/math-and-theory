module
/-
The clipped-gradient primitive and its elementary convex/quadratic lemmas are
adapted from JD-Jones-ASES/thg-gradient-curve, commit
134788107eb28be0459555383a482a350bc953a4, THGGradient/Witnesses.lean.
MIT License; original license is retained in THIRD_PARTY_LICENSE.
The strongly convex combination and its trajectory use the classical
Taylor--Hendrickx--Glineur attainer. No novelty is claimed for the examples.
-/
public import THGStrong.Sharpness
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section
open scoped InnerProductSpace

namespace THGStrong.Sharpness

/-- The clipped identity; its primitive includes both differentiable junctions. -/
def clippedGradient (τ x : ℝ) : ℝ := max (-τ) (min x τ)

def huberFunction (τ x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, clippedGradient τ t

lemma clippedGradient_lipschitz (τ : ℝ) : LipschitzWith 1 (clippedGradient τ) :=
  (LipschitzWith.id.min_const τ).const_max (-τ)

lemma clippedGradient_monotone (τ : ℝ) : Monotone (clippedGradient τ) := by
  intro x y hxy
  exact max_le_max_left _ (min_le_min_right _ hxy)

lemma huberFunction_hasDerivAt (τ x : ℝ) :
    HasDerivAt (huberFunction τ) (clippedGradient τ x) x := by
  have hc := (clippedGradient_lipschitz τ).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma huberFunction_convex (τ : ℝ) : ConvexOn ℝ Set.univ (huberFunction τ) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (huberFunction_hasDerivAt τ x).differentiableAt)
  intro x y hxy
  rw [(huberFunction_hasDerivAt τ x).deriv, (huberFunction_hasDerivAt τ y).deriv]
  exact clippedGradient_monotone τ hxy

lemma clippedGradient_zero {τ : ℝ} (hτ : 0 ≤ τ) : clippedGradient τ 0 = 0 := by
  simp [clippedGradient, min_eq_left hτ, max_eq_right (neg_nonpos.mpr hτ)]

lemma clippedGradient_of_ge {τ x : ℝ} (hτ : 0 ≤ τ) (hx : τ ≤ x) :
    clippedGradient τ x = τ := by
  rw [clippedGradient, min_eq_right hx, max_eq_right (by linarith)]

lemma scalar_minimum_of_convex_of_deriv_zero {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : HasDerivAt f 0 0) (x : ℝ) : f 0 ≤ f x := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · have hs := hf.le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hx hd
    rw [slope_def_field, sub_zero] at hs
    have ht := (le_div_iff₀ hx).mp hs
    linarith
  · rfl
  · have hs := hf.slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hx hd
    rw [slope_def_field, zero_sub] at hs
    have ht := (div_le_iff₀ (neg_pos.mpr hx)).mp hs
    linarith

lemma huberFunction_minimum {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) :
    huberFunction τ 0 ≤ huberFunction τ x := by
  apply scalar_minimum_of_convex_of_deriv_zero (huberFunction_convex τ)
  simpa only [clippedGradient_zero hτ] using huberFunction_hasDerivAt τ 0

def quadraticFunction (L x : ℝ) : ℝ := L*x^2/2

lemma quadraticFunction_hasDerivAt (L x : ℝ) :
    HasDerivAt (quadraticFunction L) (L*x) x := by
  have hd := (((hasDerivAt_id x).pow 2).const_mul L).div_const 2
  convert hd using 1
  norm_num
  ring

lemma quadraticFunction_hasGradientAt (L x : ℝ) :
    HasGradientAt (quadraticFunction L) (L*x) x :=
  (quadraticFunction_hasDerivAt L x).hasGradientAt'

lemma quadraticFunction_convex {L : ℝ} (hL : 0 ≤ L) :
    ConvexOn ℝ Set.univ (quadraticFunction L) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (quadraticFunction_hasDerivAt L x).differentiableAt)
  intro x y hxy
  rw [(quadraticFunction_hasDerivAt L x).deriv, (quadraticFunction_hasDerivAt L y).deriv]
  exact mul_le_mul_of_nonneg_left hxy hL

lemma quadraticFunction_minimum {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    quadraticFunction L 0 ≤ quadraticFunction L x := by
  simp only [quadraticFunction, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
  positivity

def stronglyConvexHuber (μ τ x : ℝ) : ℝ :=
  quadraticFunction μ x+(1-μ)*huberFunction τ x

def huberGradient (μ τ x : ℝ) : ℝ := μ*x+(1-μ)*clippedGradient τ x

lemma stronglyConvexHuber_hasGradientAt (μ τ x : ℝ) :
    HasGradientAt (stronglyConvexHuber μ τ) (huberGradient μ τ x) x :=
  ((quadraticFunction_hasDerivAt μ x).add
    ((huberFunction_hasDerivAt τ x).const_mul (1-μ))).hasGradientAt'

lemma stronglyConvexHuber_strong {μ : ℝ} (hμ : μ ≤ 1) (τ : ℝ) :
    StrongConvexOn Set.univ μ (stronglyConvexHuber μ τ) := by
  rw [strongConvexOn_iff_convex]
  have he : (fun x : ℝ => stronglyConvexHuber μ τ x-μ/2*‖x‖^2) =
      (fun x : ℝ => (1-μ)*huberFunction τ x) := by
    funext x
    simp only [stronglyConvexHuber, quadraticFunction, Real.norm_eq_abs, sq_abs]
    ring
  rw [he]
  exact (huberFunction_convex τ).smul (sub_nonneg.mpr hμ)

lemma huberGradient_lipschitz {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (τ x y : ℝ) : ‖huberGradient μ τ x-huberGradient μ τ y‖ ≤ ‖x-y‖ := by
  have hc : ‖clippedGradient τ x-clippedGradient τ y‖ ≤ ‖x-y‖ := by
    simpa only [Real.dist_eq, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
      (clippedGradient_lipschitz τ).dist_le_mul x y
  have he : huberGradient μ τ x-huberGradient μ τ y =
      μ*(x-y)+(1-μ)*(clippedGradient τ x-clippedGradient τ y) := by
    unfold huberGradient
    ring
  rw [he]
  calc
    _ ≤ ‖μ*(x-y)‖+‖(1-μ)*(clippedGradient τ x-clippedGradient τ y)‖ := norm_add_le _ _
    _ = μ*‖x-y‖+(1-μ)*‖clippedGradient τ x-clippedGradient τ y‖ := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg hμ0,
        Real.norm_of_nonneg (sub_nonneg.mpr hμ1)]
    _ ≤ μ*‖x-y‖+(1-μ)*‖x-y‖ :=
      add_le_add_left (mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hμ1)) _
    _ = _ := by ring

lemma stronglyConvexHuber_minimum {μ τ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hτ : 0 ≤ τ) (x : ℝ) : stronglyConvexHuber μ τ 0 ≤ stronglyConvexHuber μ τ x :=
  add_le_add (quadraticFunction_minimum hμ0 x)
    (mul_le_mul_of_nonneg_left (huberFunction_minimum hτ x) (sub_nonneg.mpr hμ1))

lemma huberGradient_on_trajectory {μ h : ℝ} (hh : 0 < h) (ha : 0 < 1-μ*h)
    (N i : ℕ) (hi : i ≤ N) :
    huberGradient μ (threshold μ h N) (huberPoint μ h N i) =
      μ*huberPoint μ h N i+(1-μ)*threshold μ h N := by
  rw [huberGradient, clippedGradient_of_ge (le_of_lt (threshold_pos hh ha N))
    (huberPoint_ge_threshold hh ha N i hi)]

lemma huberPoint_actual_step {μ h : ℝ} (hh : 0 < h) (ha : 0 < 1-μ*h)
    (N i : ℕ) (hi : i < N) :
    huberPoint μ h N (i+1) = huberPoint μ h N i-
      h*huberGradient μ (threshold μ h N) (huberPoint μ h N i) := by
  rw [huberGradient_on_trajectory hh ha N i (le_of_lt hi)]
  exact affinePoint_gradient_step (ne_of_gt ha) rfl i

lemma huber_terminal_gradient_norm {μ h : ℝ} (hh : 0 < h) (ha : 0 < 1-μ*h)
    (N : ℕ) :
    ‖huberGradient μ (threshold μ h N) (huberPoint μ h N N)‖ = threshold μ h N := by
  rw [huberGradient_on_trajectory hh ha N N le_rfl,
    huber_affine_gradient_terminal hh ha N,
    Real.norm_of_nonneg (le_of_lt (threshold_pos hh ha N))]

/-- A genuine differentiable one-dimensional strongly convex, 1-smooth
objective attaining the progress branch from initial distance one. -/
theorem huber_progress_attainment {μ h : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hh : 0 < h) (ha : 0 < 1-μ*h) (N : ℕ) :
    ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ),
      StrongConvexOn Set.univ μ f ∧
      (∀ z, HasGradientAt f (g z) z) ∧
      (∀ y z, ‖g y-g z‖ ≤ ‖y-z‖) ∧
      (∀ z, f 0 ≤ f z) ∧ x 0 = 1 ∧
      (∀ i < N, x (i+1) = x i-h*g (x i)) ∧
      ‖g (x N)‖ = threshold μ h N := by
  refine ⟨stronglyConvexHuber μ (threshold μ h N), huberGradient μ (threshold μ h N),
    huberPoint μ h N, stronglyConvexHuber_strong hμ1 _,
    stronglyConvexHuber_hasGradientAt μ _, huberGradient_lipschitz hμ0 hμ1 _,
    stronglyConvexHuber_minimum hμ0 hμ1 (le_of_lt (threshold_pos hh ha N)),
    ?_, huberPoint_actual_step hh ha N, huber_terminal_gradient_norm hh ha N⟩
  simp [huberPoint]

lemma unitQuadratic_strong {μ : ℝ} (hμ1 : μ ≤ 1) :
    StrongConvexOn Set.univ μ (quadraticFunction 1) := by
  rw [strongConvexOn_iff_convex]
  have he : (fun x : ℝ => quadraticFunction 1 x-μ/2*‖x‖^2) = quadraticFunction (1-μ) := by
    funext x
    simp only [quadraticFunction, Real.norm_eq_abs, sq_abs]
    ring
  rw [he]
  exact quadraticFunction_convex (sub_nonneg.mpr hμ1)

/-- The actual unit quadratic attains the oscillation branch for every step. -/
theorem quadratic_oscillation_attainment {μ : ℝ} (hμ1 : μ ≤ 1) (h : ℝ) (N : ℕ) :
    ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ),
      StrongConvexOn Set.univ μ f ∧
      (∀ z, HasGradientAt f (g z) z) ∧
      (∀ y z, ‖g y-g z‖ ≤ ‖y-z‖) ∧
      (∀ z, f 0 ≤ f z) ∧ x 0 = 1 ∧
      (∀ i < N, x (i+1) = x i-h*g (x i)) ∧
      ‖g (x N)‖ = |1-h|^N := by
  refine ⟨quadraticFunction 1, id, (fun i => (1-h)^i), unitQuadratic_strong hμ1,
    ?_, ?_, quadraticFunction_minimum (by norm_num), by simp, ?_, ?_⟩
  · intro z
    simpa only [one_mul] using quadraticFunction_hasGradientAt 1 z
  · intro y z; exact le_rfl
  · intro i _
    simp only [id_eq, pow_succ]
    ring
  · simp only [id_eq, Real.norm_eq_abs, abs_pow]

#print axioms stronglyConvexHuber_hasGradientAt
#print axioms stronglyConvexHuber_strong
#print axioms huberGradient_lipschitz
#print axioms huber_progress_attainment
#print axioms quadratic_oscillation_attainment

end THGStrong.Sharpness
