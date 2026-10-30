import CriticalHardcore.WordTrialTree

/-! A predicate-only closure of the first-danger local survival estimate. -/

set_option autoImplicit false

namespace CriticalHardcore.WordTrials

private theorem complement_probability_le (live killed total failure : ℝ)
    (htotal : 0 < total) (hsum : live + killed = total)
    (hkill : failure ≤ killed / total) : live / total ≤ 1 - failure := by
  have hh := (le_div_iff₀ htotal).mp hkill
  apply (div_le_iff₀ htotal).mpr
  nlinarith

theorem bad_trial_survival_bound {d : ℕ} [NeZero d]
    (live : List (Fin d) → Prop) (history : List (Fin d)) (h : ℕ)
    (hdead : ∀ p t : List (Fin d), ¬ live p → ¬ live (p ++ t))
    (hhalf : (words (A := Fin d) h).card ≤
      2 * (dangerousWords
        (fun p => ∃ t : List (Fin d), t.length ≤ h + 1 ∧ ¬ live (history ++ (p ++ t))) h).card) :
    ((continuations live history (2 * h + 1)).card : ℝ) / (d : ℝ) ^ (2 * h + 1) ≤
      1 - 1 / (2 * (d : ℝ) ^ (h + 1)) := by
  classical
  let dead : List (Fin d) → Prop := fun w => ¬ live (history ++ w)
  let D : List (Fin d) → Prop := fun p =>
    ∃ t : List (Fin d), t.length ≤ h + 1 ∧ dead (p ++ t)
  have hdead' : ∀ p t : List (Fin d), dead p → dead (p ++ t) := by
    intro p t hp
    simpa only [dead, List.append_assoc] using hdead (history ++ p) t hp
  have hprob := half_danger_killing_probability (0 : Fin d) D dead h (h + 1)
    hdead' (fun _ hp => hp) hhalf
  have hN : h + (h + 1) = 2 * h + 1 := by omega
  simp only [Fintype.card_fin, hN] at hprob
  have hdis : Disjoint (continuations live history (2 * h + 1))
      (deadWords dead (2 * h + 1)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hd
    have halive := ((mem_continuations _ _ _ _).mp hw).2
    exact ((mem_deadWords _ _ _).mp hd).2 halive
  have hunion : continuations live history (2 * h + 1) ∪
      deadWords dead (2 * h + 1) = words (2 * h + 1) := by
    ext w
    rw [Finset.mem_union, mem_continuations, mem_deadWords, mem_words]
    constructor
    · rintro (hw | hw) <;> exact hw.1
    · intro hw
      rcases Classical.em (live (history ++ w)) with halive | halive
      · exact Or.inl ⟨hw, halive⟩
      · exact Or.inr ⟨hw, halive⟩
  have hsplitR :
      ((continuations live history (2 * h + 1)).card : ℝ) +
      ((deadWords dead (2 * h + 1)).card : ℝ) = (d : ℝ) ^ (2 * h + 1) := by
    have hsplit : (continuations live history (2 * h + 1)).card +
        (deadWords dead (2 * h + 1)).card = d ^ (2 * h + 1) := by
      rw [← Finset.card_union_of_disjoint hdis, hunion, card_words, Fintype.card_fin]
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hsplit
    simpa only [Nat.cast_add, Nat.cast_pow] using hc
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hden : 0 < (d : ℝ) ^ (2 * h + 1) := pow_pos hdpos _
  exact complement_probability_le _ _ _ _ hden hsplitR hprob

end CriticalHardcore.WordTrials
