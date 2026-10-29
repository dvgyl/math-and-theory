import Mathlib.Tactic

namespace Kunisky

abbrev Clause (α : Type*) := Finset (α × Bool)

inductive Tree (α : Type*) where
  | leaf (C : Clause α)
  | node (v : α) (left right : Tree α)

def Tree.conclusion {α : Type*} [DecidableEq α] : Tree α → Clause α
  | .leaf C => C
  | .node v l r => (l.conclusion.erase (v, true)) ∪ (r.conclusion.erase (v, false))

def Tree.Valid {α : Type*} [DecidableEq α] (F : Finset (Clause α)) : Tree α → Prop
  | .leaf C => C ∈ F
  | .node v l r => l.Valid F ∧ r.Valid F ∧
      (v, true) ∈ l.conclusion ∧ (v, false) ∈ r.conclusion

noncomputable def Tree.mass {α : Type*} [DecidableEq α] : Tree α → Clause α → ℝ
  | .leaf D, C => if C = D then 1 else 0
  | .node _ l r, C => (l.mass C + r.mass C) / 2

theorem Tree.mass_nonneg {α : Type*} [DecidableEq α] (t : Tree α) (C : Clause α) :
    0 ≤ t.mass C := by
  induction t with
  | leaf D => simp only [mass]; split <;> norm_num
  | node v l r hl hr => exact div_nonneg (add_nonneg hl hr) (by norm_num)

theorem Tree.sum_mass {α : Type*} [DecidableEq α] {F : Finset (Clause α)}
    {t : Tree α} (h : t.Valid F) : ∑ C ∈ F, t.mass C = 1 := by
  induction t with
  | leaf D =>
      simp only [Valid] at h
      simp [mass, h]
  | node v l r hl hr =>
      simp only [Valid] at h
      simp only [mass]
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      rw [hl h.1, hr h.2.1]
      norm_num

/-- A literal `(v,b)` is satisfied when variable `v` has Boolean value `b`. -/
def SatisfiesClause {α : Type*} (assignment : α → Bool) (C : Clause α) : Prop :=
  ∃ b ∈ C, assignment b.1 = b.2

def Unsatisfiable {α : Type*} (F : Finset (Clause α)) : Prop :=
  ¬ ∃ assignment : α → Bool, ∀ C ∈ F, SatisfiesClause assignment C

theorem resolution_sound {α : Type*} [DecidableEq α]
    {a : α → Bool} {L R : Clause α} {v : α}
    (hl : SatisfiesClause a L) (hr : SatisfiesClause a R) :
    SatisfiesClause a (L.erase (v,true) ∪ R.erase (v,false)) := by
  rcases hl with ⟨⟨w,b⟩, hw, hwb⟩
  by_cases he : (w,b) = (v,true)
  · rcases hr with ⟨⟨z,c⟩, hz, hzc⟩
    have hneq : (z,c) ≠ (v,false) := by
      intro hh
      cases he
      cases hh
      simp_all
    exact ⟨(z,c), Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hneq,hz⟩), hzc⟩
  · exact ⟨(w,b), Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hw⟩), hwb⟩

theorem Tree.sound {α : Type*} [DecidableEq α] {F : Finset (Clause α)}
    {t : Tree α} (h : t.Valid F) {a : α → Bool}
    (ha : ∀ C ∈ F, SatisfiesClause a C) : SatisfiesClause a t.conclusion := by
  induction t with
  | leaf C => exact ha C h
  | node v l r hl hr => exact resolution_sound (hl h.1) (hr h.2.1)

theorem Tree.unsatisfiable {α : Type*} [DecidableEq α] {F : Finset (Clause α)}
    {t : Tree α} (h : t.Valid F) (hc : t.conclusion = ∅) : Unsatisfiable F := by
  rintro ⟨a,ha⟩
  have hh := t.sound h ha
  rw [hc] at hh
  simpa [SatisfiesClause] using hh

/-- All clauses containing exactly one literal on every variable. -/
def fullClause {α : Type*} [Fintype α] [DecidableEq α] (s : α → Bool) : Clause α :=
  Finset.univ.image fun i => (i,s i)

def fullFormula (n : ℕ) : Finset (Clause (Fin n)) :=
  Finset.univ.image (fullClause : (Fin n → Bool) → Clause (Fin n))

def positiveClause (n : ℕ) : Clause (Fin n) := fullClause (fun _ => true)

end Kunisky
