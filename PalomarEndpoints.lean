module
public import PauliConditionalExact
public import DepolarizingExact

/-! Actual-channel forms of the two exact coefficient laws.
The existence clauses retain the proved channel constructions. -/
@[expose] public section
open Matrix
open scoped BigOperators ComplexOrder
open ConditionalHockey
noncomputable section

namespace PalomarQuantum

private theorem channel_eq_of_map_eq {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N M : QuantumChannel A B) (h : N.map = M.map) : N = M := by
  cases N
  cases M
  cases h
  rfl

theorem every_pauli_channel (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    (∃ N : QuantumChannel (Fin 2) (Fin 2), N.map = PauliChannel.linear w) ∧
    ∃ a b : Fin 4, a ≠ b ∧ (∀ i, w a ≤ w i) ∧
      (∀ i, i ≠ a → w b ≤ w i) ∧
      ∀ N : QuantumChannel (Fin 2) (Fin 2), N.map = PauliChannel.linear w →
        ∀ γ : ℝ, 1 ≤ γ → conditionalCoefficient N γ =
          1 - 8 * w a * w b / (w a + w b) := by
  constructor
  · exact ⟨PauliChannel.channel w hw hsum, rfl⟩
  · obtain ⟨a, b, hab, ha, hb, hformula⟩ :=
      PauliConditionalExact.every_pauli_channel w hw hsum
    refine ⟨a, b, hab, ha, hb, ?_⟩
    intro N hN γ hγ
    have hchannel : N = PauliChannel.channel w hw hsum :=
      channel_eq_of_map_eq N _ hN
    rw [hchannel]
    exact hformula γ hγ

theorem actual_full_channel {d : ℕ} [NeZero d] (hd : 2 ≤ d) (l : ℝ)
    (hlow : -1 ≤ ((Fintype.card (DepolarizingExact.A d) : ℝ)^2 - 1) * l)
    (hhigh : l ≤ 1) :
    (∃ N : QuantumChannel (DepolarizingExact.A d) (DepolarizingExact.A d),
      ∀ X, N.map X = l • X + ((1-l)/(d:ℝ)) •
        (X.trace • (1 : Matrix (DepolarizingExact.A d) (DepolarizingExact.A d) ℂ))) ∧
    ∀ N : QuantumChannel (DepolarizingExact.A d) (DepolarizingExact.A d),
      (∀ X, N.map X = l • X + ((1-l)/(d:ℝ)) •
        (X.trace • (1 : Matrix (DepolarizingExact.A d) (DepolarizingExact.A d) ℂ))) →
      ∀ γ : ℝ, 1 ≤ γ → conditionalCoefficient N γ =
        if 0 ≤ l then l else DepolarizingEffects.sharpBound ((d:ℝ)^2) (-l) := by
  constructor
  · refine ⟨FullDepolarizingChannel.channel l hlow hhigh, ?_⟩
    intro X
    simpa only [DepolarizingExact.A, WeylBell.A, ZMod.card] using
      FullDepolarizingChannel.channel_map (A := DepolarizingExact.A d) l hlow hhigh X
  · intro N hN γ hγ
    exact DepolarizingExact.conditionalCoefficient_full hd N l
      (by simpa only [DepolarizingExact.A, WeylBell.A, ZMod.card] using hlow)
      hhigh hN γ hγ
end PalomarQuantum
end
