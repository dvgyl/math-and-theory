module
public import NegativeDepolarizingBounds
public import NegativeDepolarizingSharp
public import NegativeDepolarizingDoeblin
public import ContractionClassification


@[expose] public section

/-! Exact conditional contraction for the entire negative qubit depolarizing family. -/
open ConditionalHockey
open NegativeDepolarizingChannel

namespace NegativeDepolarizingExact
noncomputable section

/-- The conditional trace coefficient is exactly the stated rational function,
including both endpoints of the completely-positive parameter interval. -/
theorem conditional_trace_eq (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) :
    conditionalCoefficient (channel s hs hs3) 1 = s*(1+3*s)/(1-s) := by
  apply le_antisymm
  · by_cases hz : s = 0
    · subst s
      have h := PositiveReplacerSDP.conditionalCoefficient_le_one_sub_alphaPlus
        (channel 0 hs hs3) 1
      rw [NegativeDepolarizingDoeblin.alphaPlus_channel] at h
      norm_num at h ⊢
      exact h
    · by_cases he : s = 1/3
      · subst s
        have h := GeneralContraction.conditionalCoefficient_le_one (channel (1/3) hs hs3) 1
        norm_num at h ⊢
        exact h
      · have hp : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
        have hp3 : s < 1/3 := lt_of_le_of_ne hs3 he
        exact NegativeDepolarizingBounds.conditionalCoefficient_le (channel s hs hs3)
          s hp hp3 (channel_map s hs hs3) 1
  · exact NegativeDepolarizingSharp.sharpBound_le_conditionalCoefficient
      (channel s hs hs3) s (by linarith) (channel_map s hs hs3)

/-- Every conditional hockey-stick parameter at least one has the same exact
coefficient, by the checked reference-flag identity. -/
theorem conditional_hockey_eq (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3)
    (γ : ℝ) (hγ : 1 ≤ γ) :
    conditionalCoefficient (channel s hs hs3) γ = s*(1+3*s)/(1-s) := by
  rw [conditionalCoefficient_parameter_independent _ γ hγ]
  exact conditional_trace_eq s hs hs3

theorem complete_trace_eq (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) :
    GeneralContraction.completeCoefficient (channel s hs hs3) 1 = s :=
  channel_complete_trace_eq s hs hs3

theorem complete_trace_lt_conditional (s : ℝ) (hs : 0 < s) (hs3 : s ≤ 1/3) :
    GeneralContraction.completeCoefficient (channel s hs.le hs3) 1 <
      conditionalCoefficient (channel s hs.le hs3) 1 := by
  rw [complete_trace_eq, conditional_trace_eq]
  apply (lt_div_iff₀ (by linarith : 0 < 1-s)).mpr
  nlinarith [sq_pos_of_pos hs]

/-- The positive Doeblin upper bound is strictly loose at every interior
negative-depolarizing parameter. -/
theorem strict_below_doeblin_upper (s : ℝ) (hs : 0 < s) (hs3 : s < 1/3) :
    conditionalCoefficient (channel s hs.le hs3.le) 1 <
      1-PositiveReplacerSDP.alphaPlus (channel s hs.le hs3.le) := by
  rw [conditional_trace_eq, NegativeDepolarizingDoeblin.alphaPlus_channel]
  apply (div_lt_iff₀ (by linarith : 0 < 1-s)).mpr
  have h := mul_pos hs (by linarith : 0 < 1-3*s)
  nlinarith

def oneFifth : QuantumChannel (Fin 2) (Fin 2) :=
  channel (1/5) (by norm_num) (by norm_num)

theorem oneFifth_coefficients :
    GeneralContraction.completeCoefficient oneFifth 1 = 1/5 ∧
    conditionalCoefficient oneFifth 1 = 2/5 ∧
    PositiveReplacerSDP.alphaPlus oneFifth = 2/5 := by
  unfold oneFifth
  rw [complete_trace_eq, conditional_trace_eq, NegativeDepolarizingDoeblin.alphaPlus_channel]
  norm_num

def universalNOT : QuantumChannel (Fin 2) (Fin 2) :=
  channel (1/3) (by norm_num) (by norm_num)

theorem universalNOT_complete_trace :
    GeneralContraction.completeCoefficient universalNOT 1 = 1/3 := by
  exact channel_complete_trace_eq _ _ _

theorem universalNOT_conditional (γ : ℝ) (hγ : 1 ≤ γ) :
    conditionalCoefficient universalNOT γ = 1 := by
  unfold universalNOT
  rw [conditional_hockey_eq _ _ _ γ hγ]
  norm_num

theorem universalNOT_complete_hockey (γ : ℝ) (hγ : 1 < γ) :
    GeneralContraction.completeCoefficient universalNOT γ = 1 := by
  apply (ContractionClassification.complete_saturated_iff universalNOT γ hγ).mpr
  exact NegativeDepolarizingDoeblin.universal_not_alphaPlus_zero

end
end NegativeDepolarizingExact
