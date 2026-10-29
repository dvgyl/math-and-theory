import FullFormulaProperties

namespace Kunisky

/-- Zero coalesced mass means an axiom was never used, so it can be deleted. -/
lemma Tree.valid_erase_of_mass_zero {α : Type*} [DecidableEq α]
    {F : Finset (Clause α)} {t : Tree α} (ht : t.Valid F) (C : Clause α)
    (hz : t.mass C = 0) : t.Valid (F.erase C) := by
  induction t with
  | leaf D =>
      have hne : D ≠ C := by
        intro he
        subst D
        simp [Tree.mass] at hz
      exact Finset.mem_erase.mpr ⟨hne,ht⟩
  | node v l r hl hr =>
      have hln := l.mass_nonneg C
      have hrn := r.mass_nonneg C
      have hlz : l.mass C = 0 := by
        change (l.mass C + r.mass C) / 2 = 0 at hz
        linarith
      have hrz : r.mass C = 0 := by
        change (l.mass C + r.mass C) / 2 = 0 at hz
        linarith
      exact ⟨hl ht.1 hlz, hr ht.2.1 hrz, ht.2.2⟩

/-- Every axiom has positive mass in every refutation of a minimally
unsatisfiable formula. In particular, every effective depth is finite. -/
theorem Tree.mass_pos_of_minimal {α : Type*} [DecidableEq α]
    {F : Finset (Clause α)} (hF : MinimallyUnsatisfiable F)
    {t : Tree α} (ht : t.Valid F) (hc : t.conclusion = ∅)
    {C : Clause α} (hC : C ∈ F) : 0 < t.mass C := by
  by_contra hp
  have hz : t.mass C = 0 := le_antisymm (not_lt.mp hp) (t.mass_nonneg C)
  have he := t.valid_erase_of_mass_zero ht C hz
  exact t.unsatisfiable he hc (hF.2 C hC)

theorem fullFormula_mass_pos {n : ℕ} {t : Tree (Fin n)}
    (ht : t.Valid (fullFormula n)) (hc : t.conclusion = ∅)
    (s : Fin n → Bool) : 0 < t.mass (fullClause s) := by
  apply t.mass_pos_of_minimal (fullFormula_minimallyUnsatisfiable n) ht hc
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩

end Kunisky
