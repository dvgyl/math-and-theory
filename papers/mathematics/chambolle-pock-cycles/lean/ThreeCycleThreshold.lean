import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace CPSharpness

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Squared displacement over the three edges of a closed orbit. -/
def cycleEnergy (x₀ x₁ x₂ : E) : ℝ :=
  ‖x₀ - x₁‖ ^ 2 + ‖x₁ - x₂‖ ^ 2 + ‖x₂ - x₀‖ ^ 2

/-- The sum of primal supporting inequalities around one orientation of a three-cycle. -/
def primalCycleForm (x₀ x₁ x₂ : E) (a₀ a₁ a₂ y₀ y₁ y₂ : F) : ℝ :=
  (⟪x₂ - x₀, x₁ - x₀⟫ - ⟪y₂, a₁ - a₀⟫) +
  (⟪x₀ - x₁, x₂ - x₁⟫ - ⟪y₀, a₂ - a₁⟫) +
  (⟪x₁ - x₂, x₀ - x₂⟫ - ⟪y₁, a₀ - a₂⟫)

/-- The corresponding dual supporting sum, with `κ` multiplying the extrapolated primal value. -/
def dualCycleForm (κ θ : ℝ) (a₀ a₁ a₂ y₀ y₁ y₂ : F) : ℝ :=
  ⟪y₂ + κ • ((1 + θ) • a₀ - θ • a₂) - y₀, y₁ - y₀⟫ +
  ⟪y₀ + κ • ((1 + θ) • a₁ - θ • a₀) - y₁, y₂ - y₁⟫ +
  ⟪y₁ + κ • ((1 + θ) • a₂ - θ • a₁) - y₂, y₀ - y₂⟫

/-- The exact polynomial boundary for nonconstant three-periodic PDHG orbits. -/
def threeCyclePolynomial (κ θ : ℝ) : ℝ :=
  κ ^ 2 * (1 + θ) ^ 2 - 2 * κ * (1 + 3 * θ) - 3

private noncomputable def squareSum (κ θ : ℝ) (a₀ a₁ a₂ y₀ y₁ y₂ : F) : ℝ :=
  ‖(y₀ - y₁) - (κ * (1 + θ) / 2) • (a₀ - a₁) -
    (1 / 2 : ℝ) • ((2 : ℝ) • a₂ - a₀ - a₁)‖ ^ 2 +
  ‖(y₁ - y₂) - (κ * (1 + θ) / 2) • (a₁ - a₂) -
    (1 / 2 : ℝ) • ((2 : ℝ) • a₀ - a₁ - a₂)‖ ^ 2 +
  ‖(y₂ - y₀) - (κ * (1 + θ) / 2) • (a₂ - a₀) -
    (1 / 2 : ℝ) • ((2 : ℝ) • a₁ - a₂ - a₀)‖ ^ 2

private theorem squareSum_nonneg (κ θ : ℝ) (a₀ a₁ a₂ y₀ y₁ y₂ : F) :
    0 ≤ squareSum κ θ a₀ a₁ a₂ y₀ y₁ y₂ := by
  unfold squareSum
  positivity

/-- An exact algebraic certificate; no property of convex functions enters this identity. -/
theorem threeCycle_sos_identity (κ θ : ℝ) (x₀ x₁ x₂ : E)
    (a₀ a₁ a₂ y₀ y₁ y₂ : F) :
    threeCyclePolynomial κ θ * cycleEnergy x₀ x₁ x₂ =
      4 * squareSum κ θ a₀ a₁ a₂ y₀ y₁ y₂ -
      8 * dualCycleForm κ θ a₀ a₁ a₂ y₀ y₁ y₂ -
      4 * (3 + κ * (1 + 3 * θ)) * primalCycleForm x₀ x₁ x₂ a₀ a₁ a₂ y₀ y₁ y₂ +
      (κ ^ 2 * (1 + θ) ^ 2 + 3) * (cycleEnergy x₀ x₁ x₂ - cycleEnergy a₀ a₁ a₂) := by
  unfold threeCyclePolynomial cycleEnergy squareSum primalCycleForm dualCycleForm
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

omit [InnerProductSpace ℝ E] in
lemma cycleEnergy_nonneg (x₀ x₁ x₂ : E) : 0 ≤ cycleEnergy x₀ x₁ x₂ := by
  unfold cycleEnergy
  positivity

omit [InnerProductSpace ℝ E] in
lemma cycleEnergy_eq_zero_iff (x₀ x₁ x₂ : E) :
    cycleEnergy x₀ x₁ x₂ = 0 ↔ x₀ = x₁ ∧ x₁ = x₂ := by
  constructor
  · intro h
    have h₀ : ‖x₀ - x₁‖ = 0 := by
      unfold cycleEnergy at h
      nlinarith [sq_nonneg ‖x₀ - x₁‖, sq_nonneg ‖x₁ - x₂‖, sq_nonneg ‖x₂ - x₀‖]
    have h₁ : ‖x₁ - x₂‖ = 0 := by
      unfold cycleEnergy at h
      nlinarith [sq_nonneg ‖x₀ - x₁‖, sq_nonneg ‖x₁ - x₂‖, sq_nonneg ‖x₂ - x₀‖]
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp h₀), sub_eq_zero.mp (norm_eq_zero.mp h₁)⟩
  · rintro ⟨rfl, rfl⟩
    simp [cycleEnergy]

/-- Universal three-cycle exclusion from the actual cyclic supporting sums and a contraction. -/
theorem threeCycle_polynomial_nonneg_of_forms {κ θ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (x₀ x₁ x₂ : E) (a₀ a₁ a₂ y₀ y₁ y₂ : F)
    (hx : ¬ (x₀ = x₁ ∧ x₁ = x₂))
    (hA : primalCycleForm x₀ x₁ x₂ a₀ a₁ a₂ y₀ y₁ y₂ ≤ 0)
    (hB : dualCycleForm κ θ a₀ a₁ a₂ y₀ y₁ y₂ ≤ 0)
    (hL : cycleEnergy a₀ a₁ a₂ ≤ cycleEnergy x₀ x₁ x₂) :
    0 ≤ threeCyclePolynomial κ θ := by
  have hU : 0 < cycleEnergy x₀ x₁ x₂ :=
    lt_of_le_of_ne (cycleEnergy_nonneg _ _ _) (fun h => hx ((cycleEnergy_eq_zero_iff _ _ _).mp h.symm))
  have hcoef : 0 ≤ 4 * (3 + κ * (1 + 3 * θ)) := by positivity
  have hcoef' : 0 ≤ κ ^ 2 * (1 + θ) ^ 2 + 3 := by positivity
  have hA' := mul_nonpos_of_nonneg_of_nonpos hcoef hA
  have hL' := mul_nonneg hcoef' (sub_nonneg.mpr hL)
  have hS := squareSum_nonneg κ θ a₀ a₁ a₂ y₀ y₁ y₂
  have hid := threeCycle_sos_identity κ θ x₀ x₁ x₂ a₀ a₁ a₂ y₀ y₁ y₂
  have hprod : 0 ≤ threeCyclePolynomial κ θ * cycleEnergy x₀ x₁ x₂ := by nlinarith
  exact nonneg_of_mul_nonneg_left hprod hU

end CPSharpness
