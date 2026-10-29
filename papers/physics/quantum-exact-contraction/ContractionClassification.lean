import UniversalContraction
import PositiveReplacerSDP

/-! Final strictness classification in terms of the actual finite Doeblin SDP. -/
open ConditionalHockey PositiveReplacerSDP

namespace ContractionClassification
noncomputable section
variable {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B]

/-- The reference type used by the explicit construction in
`UniversalContraction.complete_eq_one_of_no_positiveReplacer`. -/
abbrev saturationReference (A : Type) := Bool × (Option (A × (A × Bool)) × A)

omit [DecidableEq A] [Nonempty A] in
theorem saturationReference_card [DecidableEq A] [Nonempty A] :
    Fintype.card (saturationReference A) = 4 * (Fintype.card A)^3 + 2 * Fintype.card A := by
  simp only [saturationReference, Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
  ring

theorem complete_strict_iff (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 < γ) :
    GeneralContraction.completeCoefficient N γ < 1 ↔ 0 < alphaPlus N := by
  rw [UniversalContraction.complete_lt_one_iff_positiveReplacer N γ hγ,
    alphaPlus_pos_iff]

theorem complete_saturated_iff (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 < γ) :
    GeneralContraction.completeCoefficient N γ = 1 ↔ alphaPlus N = 0 := by
  rw [UniversalContraction.complete_eq_one_iff_no_positiveReplacer N γ hγ,
    alphaPlus_eq_zero_iff]

theorem conditional_strict_iff (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ) :
    conditionalCoefficient N γ < 1 ↔ 0 < alphaPlus N := by
  rw [UniversalContraction.conditional_lt_one_iff_positiveReplacer N γ hγ,
    alphaPlus_pos_iff]

theorem conditional_saturated_iff (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ) :
    conditionalCoefficient N γ = 1 ↔ alphaPlus N = 0 := by
  rw [UniversalContraction.conditional_eq_one_iff_no_positiveReplacer N γ hγ,
    alphaPlus_eq_zero_iff]

theorem conditional_trace_strict_iff (N : QuantumChannel A B) :
    conditionalCoefficient N 1 < 1 ↔ 0 < alphaPlus N :=
  conditional_strict_iff N 1 (le_refl _)

theorem conditional_trace_saturated_iff (N : QuantumChannel A B) :
    conditionalCoefficient N 1 = 1 ↔ alphaPlus N = 0 :=
  conditional_saturated_iff N 1 (le_refl _)

end
end ContractionClassification
