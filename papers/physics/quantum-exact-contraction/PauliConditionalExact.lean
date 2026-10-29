import PauliConditionalUpper
import PauliConditionalLower
import PauliSymmetry
import PauliMinimumPair

/-! Exact conditional trace and hockey-stick contraction for every Pauli channel. -/
open ConditionalHockey

namespace PauliConditionalExact
noncomputable section

/-- The coefficient depends only on the two smallest Pauli weights, with
multiplicity. Division by zero has the continuous boundary value specified
by the expression: if both selected weights are zero, the result is one. -/
theorem conditional_trace_eq_of_minimal_pair (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (a b : Fin 4) (hab : a ≠ b) (ha : ∀ i, w a ≤ w i)
    (hb : ∀ i, i ≠ a → w b ≤ w i) :
    conditionalCoefficient (PauliChannel.channel w hw hsum) 1 =
      1-8*w a*w b/(w a+w b) := by
  let e := PauliSymmetry.normalizingEquiv a b
  let v := fun i => w (e.symm i)
  have hv : ∀ i, 0 ≤ v i := PauliSymmetry.relabel_nonneg w hw e
  have hvs : ∑ i, v i = 1 := PauliSymmetry.relabel_sum w hsum e
  have hv0 : v 0 = w a := by
    simp only [v,e,PauliSymmetry.normalizingEquiv_symm_zero]
  have hv3 : v 3 = w b := by
    simp only [v,e,PauliSymmetry.normalizingEquiv_symm_three a b hab]
  have hneq (i : Fin 4) (hi : i ≠ 0) : e.symm i ≠ a := by
    intro he
    have hh := congrArg e he
    simp only [Equiv.apply_symm_apply,e,PauliSymmetry.normalizingEquiv_apply_left] at hh
    exact hi hh
  have h03 : v 0 ≤ v 3 := by rw [hv0,hv3]; exact ha b
  have h31 : v 3 ≤ v 1 := by
    rw [hv3]
    exact hb (e.symm 1) (hneq 1 (by decide))
  have h32 : v 3 ≤ v 2 := by
    rw [hv3]
    exact hb (e.symm 2) (hneq 2 (by decide))
  have hupper := PauliConditionalUpper.coefficient_le_pairBound v hv hvs h03 h31 h32
  have hlower := PauliConditionalLower.channel_pairBound_le v hv hvs
  have heq := le_antisymm hupper hlower
  have hequiv : conditionalCoefficient (PauliChannel.channel v hv hvs) 1 =
      conditionalCoefficient (PauliChannel.channel w hw hsum) 1 :=
    PauliSymmetry.conditionalCoefficient_normalize w hw hsum a b 1
  rw [hequiv,hv0,hv3] at heq
  exact heq

theorem conditional_hockey_eq_of_minimal_pair (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (a b : Fin 4) (hab : a ≠ b) (ha : ∀ i, w a ≤ w i)
    (hb : ∀ i, i ≠ a → w b ≤ w i) (γ : ℝ) (hγ : 1 ≤ γ) :
    conditionalCoefficient (PauliChannel.channel w hw hsum) γ =
      1-8*w a*w b/(w a+w b) := by
  rw [conditionalCoefficient_parameter_independent _ γ hγ]
  exact conditional_trace_eq_of_minimal_pair w hw hsum a b hab ha hb

/-- Every probability vector admits the stated exact formula, including all
ties and every boundary face of the probability simplex. -/
theorem every_pauli_channel (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ a b : Fin 4, a ≠ b ∧ (∀ i, w a ≤ w i) ∧
      (∀ i, i ≠ a → w b ≤ w i) ∧
      ∀ γ : ℝ, 1 ≤ γ →
        conditionalCoefficient (PauliChannel.channel w hw hsum) γ =
          1-8*w a*w b/(w a+w b) := by
  obtain ⟨a,b,hab,ha,hb⟩ := PauliMinimumPair.exists_minimal_pair w
  exact ⟨a,b,hab,ha,hb,conditional_hockey_eq_of_minimal_pair w hw hsum a b hab ha hb⟩

end
end PauliConditionalExact
