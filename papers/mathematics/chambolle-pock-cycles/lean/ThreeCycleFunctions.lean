import Proximal
import ThreeCycleThreshold

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace CPSharpness

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

omit [CompleteSpace E] [CompleteSpace F] in
lemma cycleEnergy_map_le (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (x₀ x₁ x₂ : E) :
    cycleEnergy (L x₀) (L x₁) (L x₂) ≤ cycleEnergy x₀ x₁ x₂ := by
  have h (z : E) : ‖L z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    have hn : ‖L z‖ ≤ ‖z‖ := calc
      ‖L z‖ ≤ ‖L‖ * ‖z‖ := L.le_opNorm z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg z)
      _ = ‖z‖ := one_mul _
    nlinarith [norm_nonneg (L z), norm_nonneg z]
  unfold cycleEnergy
  simpa only [map_sub] using add_le_add (add_le_add (h (x₀ - x₁)) (h (x₁ - x₂))) (h (x₂ - x₀))

omit [CompleteSpace F] in
lemma dualCycleForm_same_primal (κ θ : ℝ) (a y₀ y₁ y₂ : F) :
    dualCycleForm κ θ a a a y₀ y₁ y₂ = cycleEnergy y₀ y₁ y₂ / 2 := by
  unfold dualCycleForm cycleEnergy
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

/-- Every nonconstant, actual period-three proximal orbit of Chambolle--Pock with a
contractive linear operator obeys the exact polynomial boundary. The functions are
arbitrary convex functions on their convex effective domains. No saddle, compactness,
regularity, or convergence assumption is needed for this necessary condition. -/
theorem proximal_three_cycle_polynomial_nonneg
    {C : Set E} {D : Set F} {f : E → ℝ} {g : F → ℝ}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {κ θ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (x₀ x₁ x₂ : E) (y₀ y₁ y₂ : F)
    (hx₀ : IsProx C f (x₂ - L.adjoint y₂) x₀)
    (hx₁ : IsProx C f (x₀ - L.adjoint y₀) x₁)
    (hx₂ : IsProx C f (x₁ - L.adjoint y₁) x₂)
    (hy₀ : IsProx D (fun y => κ * g y)
      (y₂ + κ • ((1 + θ) • L x₀ - θ • L x₂)) y₀)
    (hy₁ : IsProx D (fun y => κ * g y)
      (y₀ + κ • ((1 + θ) • L x₁ - θ • L x₀)) y₁)
    (hy₂ : IsProx D (fun y => κ * g y)
      (y₁ + κ • ((1 + θ) • L x₂ - θ • L x₁)) y₂)
    (hne : ¬ (x₀ = x₁ ∧ x₁ = x₂ ∧ y₀ = y₁ ∧ y₁ = y₂)) :
    0 ≤ threeCyclePolynomial κ θ := by
  have hgκ : ConvexOn ℝ D (fun y => κ * g y) := by
    simpa only [smul_eq_mul] using hg.smul hκ
  have sx₀ := supports_of_isProx hf hx₀
  have sx₁ := supports_of_isProx hf hx₁
  have sx₂ := supports_of_isProx hf hx₂
  have sy₀ := supports_of_isProx hgκ hy₀
  have sy₁ := supports_of_isProx hgκ hy₁
  have sy₂ := supports_of_isProx hgκ hy₂
  have hA : primalCycleForm x₀ x₁ x₂ (L x₀) (L x₁) (L x₂) y₀ y₁ y₂ ≤ 0 := by
    have h₀ := sx₀.2 x₁ sx₁.1
    have h₁ := sx₁.2 x₂ sx₂.1
    have h₂ := sx₂.2 x₀ sx₀.1
    have he₀ : x₂ - L.adjoint y₂ - x₀ = (x₂ - x₀) - L.adjoint y₂ := by abel
    have he₁ : x₀ - L.adjoint y₀ - x₁ = (x₀ - x₁) - L.adjoint y₀ := by abel
    have he₂ : x₁ - L.adjoint y₁ - x₂ = (x₁ - x₂) - L.adjoint y₁ := by abel
    rw [he₀, inner_sub_left, L.adjoint_inner_left, map_sub] at h₀
    rw [he₁, inner_sub_left, L.adjoint_inner_left, map_sub] at h₁
    rw [he₂, inner_sub_left, L.adjoint_inner_left, map_sub] at h₂
    unfold primalCycleForm
    linarith
  have hB : dualCycleForm κ θ (L x₀) (L x₁) (L x₂) y₀ y₁ y₂ ≤ 0 := by
    have h₀ := sy₀.2 y₁ sy₁.1
    have h₁ := sy₁.2 y₂ sy₂.1
    have h₂ := sy₂.2 y₀ sy₀.1
    unfold dualCycleForm
    linarith
  by_cases hx : x₀ = x₁ ∧ x₁ = x₂
  · rcases hx with ⟨rfl, rfl⟩
    rw [dualCycleForm_same_primal] at hB
    have hy : cycleEnergy y₀ y₁ y₂ = 0 :=
      le_antisymm (by linarith) (cycleEnergy_nonneg _ _ _)
    rcases (cycleEnergy_eq_zero_iff _ _ _).mp hy with ⟨hy₀₁, hy₁₂⟩
    exact False.elim (hne ⟨rfl, rfl, hy₀₁, hy₁₂⟩)
  · exact threeCycle_polynomial_nonneg_of_forms hκ hθ x₀ x₁ x₂ (L x₀) (L x₁) (L x₂)
      y₀ y₁ y₂ hx hA hB (cycleEnergy_map_le L hL _ _ _)

end CPSharpness

#print axioms CPSharpness.proximal_three_cycle_polynomial_nonneg
