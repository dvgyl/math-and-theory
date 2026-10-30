import ThreeCycleFunctions
import Mathlib.Tactic.FieldSimp

/-!
# The actual step-size product for period-three Chambolle--Pock orbits

This module verifies the normalization algebra directly on the supporting sums of
the actual proximal updates.  The primal and dual steps remain `τ` and `σ` in the
premises; the conclusion uses exactly `τ * σ * ‖L‖ ^ 2`.
-/

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

noncomputable section

namespace CPSharpness

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

theorem primalCycleForm_normalize (τ r : ℝ) (hr : r ≠ 0)
    (x₀ x₁ x₂ : E) (a₀ a₁ a₂ y₀ y₁ y₂ : F) :
    primalCycleForm x₀ x₁ x₂ (r⁻¹ • a₀) (r⁻¹ • a₁) (r⁻¹ • a₂)
      ((τ * r) • y₀) ((τ * r) • y₁) ((τ * r) • y₂) =
    primalCycleForm x₀ x₁ x₂ a₀ a₁ a₂ (τ • y₀) (τ • y₁) (τ • y₂) := by
  unfold primalCycleForm
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  field_simp [hr]
  ring

theorem dualCycleForm_normalize (τ σ θ r : ℝ) (hr : r ≠ 0)
    (a₀ a₁ a₂ y₀ y₁ y₂ : F) :
    dualCycleForm (τ * σ * r ^ 2) θ (r⁻¹ • a₀) (r⁻¹ • a₁) (r⁻¹ • a₂)
      ((τ * r) • y₀) ((τ * r) • y₁) ((τ * r) • y₂) =
    (τ * r) ^ 2 * dualCycleForm σ θ a₀ a₁ a₂ y₀ y₁ y₂ := by
  unfold dualCycleForm
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  field_simp [hr]
  ring

theorem normalized_operator_cycleEnergy_le (L : E →L[ℝ] F) (hr : 0 < ‖L‖)
    (x₀ x₁ x₂ : E) :
    cycleEnergy (‖L‖⁻¹ • L x₀) (‖L‖⁻¹ • L x₁) (‖L‖⁻¹ • L x₂) ≤
      cycleEnergy x₀ x₁ x₂ := by
  have h (z : E) : ‖‖L‖⁻¹ • L z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    have hn : ‖‖L‖⁻¹ • L z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      calc
        ‖L‖⁻¹ * ‖L z‖ ≤ ‖L‖⁻¹ * (‖L‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left (L.le_opNorm z) (le_of_lt (inv_pos.mpr hr))
        _ = ‖z‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]
    nlinarith [norm_nonneg (‖L‖⁻¹ • L z), norm_nonneg z]
  unfold cycleEnergy
  simpa only [map_sub, smul_sub] using
    add_le_add (add_le_add (h (x₀ - x₁)) (h (x₁ - x₂))) (h (x₂ - x₀))

variable [CompleteSpace E] [CompleteSpace F]

/-- A nonconstant actual three-cycle forces the sharp polynomial restriction on
the genuine step-size product, for arbitrary nonzero bounded linear coupling. -/
theorem general_step_three_cycle_polynomial_nonneg
    {C : Set E} {D : Set F} {f : E → ℝ} {g : F → ℝ}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (L : E →L[ℝ] F) (hL : 0 < ‖L‖)
    {τ σ θ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hθ : 0 ≤ θ)
    (x₀ x₁ x₂ : E) (y₀ y₁ y₂ : F)
    (hx₀ : IsProx C (fun x => τ * f x) (x₂ - τ • L.adjoint y₂) x₀)
    (hx₁ : IsProx C (fun x => τ * f x) (x₀ - τ • L.adjoint y₀) x₁)
    (hx₂ : IsProx C (fun x => τ * f x) (x₁ - τ • L.adjoint y₁) x₂)
    (hy₀ : IsProx D (fun y => σ * g y)
      (y₂ + σ • ((1 + θ) • L x₀ - θ • L x₂)) y₀)
    (hy₁ : IsProx D (fun y => σ * g y)
      (y₀ + σ • ((1 + θ) • L x₁ - θ • L x₀)) y₁)
    (hy₂ : IsProx D (fun y => σ * g y)
      (y₁ + σ • ((1 + θ) • L x₂ - θ • L x₁)) y₂)
    (hne : ¬ (x₀ = x₁ ∧ x₁ = x₂ ∧ y₀ = y₁ ∧ y₁ = y₂)) :
    0 ≤ threeCyclePolynomial (τ * σ * ‖L‖ ^ 2) θ := by
  have hfτ : ConvexOn ℝ C (fun x => τ * f x) := by
    simpa only [smul_eq_mul] using hf.smul hτ.le
  have hgσ : ConvexOn ℝ D (fun y => σ * g y) := by
    simpa only [smul_eq_mul] using hg.smul hσ.le
  have sx₀ := supports_of_isProx hfτ hx₀
  have sx₁ := supports_of_isProx hfτ hx₁
  have sx₂ := supports_of_isProx hfτ hx₂
  have sy₀ := supports_of_isProx hgσ hy₀
  have sy₁ := supports_of_isProx hgσ hy₁
  have sy₂ := supports_of_isProx hgσ hy₂
  have hA : primalCycleForm x₀ x₁ x₂ (L x₀) (L x₁) (L x₂)
      (τ • y₀) (τ • y₁) (τ • y₂) ≤ 0 := by
    have h₀ := sx₀.2 x₁ sx₁.1
    have h₁ := sx₁.2 x₂ sx₂.1
    have h₂ := sx₂.2 x₀ sx₀.1
    have he₀ : x₂ - τ • L.adjoint y₂ - x₀ = (x₂ - x₀) - τ • L.adjoint y₂ := by abel
    have he₁ : x₀ - τ • L.adjoint y₀ - x₁ = (x₀ - x₁) - τ • L.adjoint y₀ := by abel
    have he₂ : x₁ - τ • L.adjoint y₁ - x₂ = (x₁ - x₂) - τ • L.adjoint y₁ := by abel
    rw [he₀, inner_sub_left, real_inner_smul_left, L.adjoint_inner_left, map_sub] at h₀
    rw [he₁, inner_sub_left, real_inner_smul_left, L.adjoint_inner_left, map_sub] at h₁
    rw [he₂, inner_sub_left, real_inner_smul_left, L.adjoint_inner_left, map_sub] at h₂
    unfold primalCycleForm
    simp only [real_inner_smul_left]
    linarith
  have hB : dualCycleForm σ θ (L x₀) (L x₁) (L x₂) y₀ y₁ y₂ ≤ 0 := by
    have h₀ := sy₀.2 y₁ sy₁.1
    have h₁ := sy₁.2 y₂ sy₂.1
    have h₂ := sy₂.2 y₀ sy₀.1
    unfold dualCycleForm
    linarith
  have hx : ¬ (x₀ = x₁ ∧ x₁ = x₂) := by
    rintro ⟨rfl, rfl⟩
    rw [dualCycleForm_same_primal] at hB
    have hy : cycleEnergy y₀ y₁ y₂ = 0 :=
      le_antisymm (by linarith) (cycleEnergy_nonneg _ _ _)
    rcases (cycleEnergy_eq_zero_iff _ _ _).mp hy with ⟨hy₀₁, hy₁₂⟩
    exact hne ⟨rfl, rfl, hy₀₁, hy₁₂⟩
  have hAn : primalCycleForm x₀ x₁ x₂ (‖L‖⁻¹ • L x₀) (‖L‖⁻¹ • L x₁)
      (‖L‖⁻¹ • L x₂) ((τ * ‖L‖) • y₀) ((τ * ‖L‖) • y₁) ((τ * ‖L‖) • y₂) ≤ 0 := by
    rw [primalCycleForm_normalize τ ‖L‖ (ne_of_gt hL)]
    exact hA
  have hBn : dualCycleForm (τ * σ * ‖L‖ ^ 2) θ (‖L‖⁻¹ • L x₀) (‖L‖⁻¹ • L x₁)
      (‖L‖⁻¹ • L x₂) ((τ * ‖L‖) • y₀) ((τ * ‖L‖) • y₁) ((τ * ‖L‖) • y₂) ≤ 0 := by
    rw [dualCycleForm_normalize τ σ θ ‖L‖ (ne_of_gt hL)]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hB
  exact threeCycle_polynomial_nonneg_of_forms (by positivity) hθ x₀ x₁ x₂
    (‖L‖⁻¹ • L x₀) (‖L‖⁻¹ • L x₁) (‖L‖⁻¹ • L x₂)
    ((τ * ‖L‖) • y₀) ((τ * ‖L‖) • y₁) ((τ * ‖L‖) • y₂) hx hAn hBn
    (normalized_operator_cycleEnergy_le L hL x₀ x₁ x₂)

omit [CompleteSpace E] in
/-- A genuine proximal map of a convex function has no nonconstant three-cycle. -/
theorem proximal_three_cycle_constant {K : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (x₀ x₁ x₂ : E)
    (hx₀ : IsProx K f x₂ x₀) (hx₁ : IsProx K f x₀ x₁) (hx₂ : IsProx K f x₁ x₂) :
    x₀ = x₁ ∧ x₁ = x₂ := by
  have s₀ := supports_of_isProx hf hx₀
  have s₁ := supports_of_isProx hf hx₁
  have s₂ := supports_of_isProx hf hx₂
  have h₀ := s₀.2 x₁ s₁.1
  have h₁ := s₁.2 x₂ s₂.1
  have h₂ := s₂.2 x₀ s₀.1
  have hb : dualCycleForm 0 0 (0 : E) 0 0 x₀ x₁ x₂ ≤ 0 := by
    unfold dualCycleForm
    simp only [zero_smul, add_zero]
    linarith
  rw [dualCycleForm_same_primal] at hb
  apply (cycleEnergy_eq_zero_iff x₀ x₁ x₂).mp
  exact le_antisymm (by linarith) (cycleEnergy_nonneg _ _ _)

/-- The exact general step-size product condition, including the zero operator.
Every premise is an actual proximal minimization with its original step size. -/
theorem step_product_three_cycle_polynomial_nonneg
    {C : Set E} {D : Set F} {f : E → ℝ} {g : F → ℝ}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (L : E →L[ℝ] F)
    {τ σ θ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hθ : 0 ≤ θ)
    (x₀ x₁ x₂ : E) (y₀ y₁ y₂ : F)
    (hx₀ : IsProx C (fun x => τ * f x) (x₂ - τ • L.adjoint y₂) x₀)
    (hx₁ : IsProx C (fun x => τ * f x) (x₀ - τ • L.adjoint y₀) x₁)
    (hx₂ : IsProx C (fun x => τ * f x) (x₁ - τ • L.adjoint y₁) x₂)
    (hy₀ : IsProx D (fun y => σ * g y)
      (y₂ + σ • ((1 + θ) • L x₀ - θ • L x₂)) y₀)
    (hy₁ : IsProx D (fun y => σ * g y)
      (y₀ + σ • ((1 + θ) • L x₁ - θ • L x₀)) y₁)
    (hy₂ : IsProx D (fun y => σ * g y)
      (y₁ + σ • ((1 + θ) • L x₂ - θ • L x₁)) y₂)
    (hne : ¬ (x₀ = x₁ ∧ x₁ = x₂ ∧ y₀ = y₁ ∧ y₁ = y₂)) :
    0 ≤ threeCyclePolynomial (τ * σ * ‖L‖ ^ 2) θ := by
  by_cases hL : L = 0
  · subst L
    simp only [map_zero, ContinuousLinearMap.zero_apply, smul_zero, sub_zero, add_zero]
      at hx₀ hx₁ hx₂ hy₀ hy₁ hy₂
    have hfτ : ConvexOn ℝ C (fun x => τ * f x) := by
      simpa only [smul_eq_mul] using hf.smul hτ.le
    have hgσ : ConvexOn ℝ D (fun y => σ * g y) := by
      simpa only [smul_eq_mul] using hg.smul hσ.le
    obtain ⟨hx01, hx12⟩ := proximal_three_cycle_constant hfτ x₀ x₁ x₂ hx₀ hx₁ hx₂
    obtain ⟨hy01, hy12⟩ := proximal_three_cycle_constant hgσ y₀ y₁ y₂ hy₀ hy₁ hy₂
    exact False.elim (hne ⟨hx01, hx12, hy01, hy12⟩)
  · exact general_step_three_cycle_polynomial_nonneg hf hg L (norm_pos_iff.mpr hL)
      hτ hσ hθ x₀ x₁ x₂ y₀ y₁ y₂ hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hne

end CPSharpness

#print axioms CPSharpness.general_step_three_cycle_polynomial_nonneg
#print axioms CPSharpness.step_product_three_cycle_polynomial_nonneg
