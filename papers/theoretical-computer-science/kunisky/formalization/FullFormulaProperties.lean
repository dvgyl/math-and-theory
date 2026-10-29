import Conjecture

namespace Kunisky

lemma mem_fullClause_iff {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → Bool) (i : α) (b : Bool) :
    (i,b) ∈ fullClause s ↔ s i = b := by
  simp [fullClause]

lemma satisfies_fullClause_iff {α : Type*} [Fintype α] [DecidableEq α]
    (a s : α → Bool) : SatisfiesClause a (fullClause s) ↔ ∃ i, a i = s i := by
  constructor
  · rintro ⟨⟨i,b⟩, hm, he⟩
    rw [mem_fullClause_iff] at hm
    exact ⟨i, he.trans hm.symm⟩
  · rintro ⟨i,hi⟩
    exact ⟨(i,s i), mem_fullClause s i, hi⟩

lemma complement_falsifies_fullClause {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → Bool) : ¬ SatisfiesClause (fun i => !(s i)) (fullClause s) := by
  rw [satisfies_fullClause_iff]
  rintro ⟨i,hi⟩
  cases hs : s i <;> simp [hs] at hi

lemma fullFormula_unsatisfiable (n : ℕ) : Unsatisfiable (fullFormula n) := by
  rintro ⟨a,ha⟩
  have hm : fullClause (fun i => !(a i)) ∈ fullFormula n :=
    Finset.mem_image.mpr ⟨(fun i => !(a i)), Finset.mem_univ _, rfl⟩
  have hs := ha _ hm
  rw [satisfies_fullClause_iff] at hs
  rcases hs with ⟨i,hi⟩
  cases hh : a i <;> simp [hh] at hi

/-- Removing any one clause admits an explicit satisfying assignment. -/
lemma fullFormula_erase_satisfiable {n : ℕ} {C : Clause (Fin n)}
    (hC : C ∈ fullFormula n) :
    ∃ a : Fin n → Bool, ∀ D ∈ (fullFormula n).erase C, SatisfiesClause a D := by
  rcases Finset.mem_image.mp hC with ⟨s,_,rfl⟩
  refine ⟨fun i => !(s i), ?_⟩
  intro D hD
  rcases Finset.mem_erase.mp hD with ⟨hne,hm⟩
  rcases Finset.mem_image.mp hm with ⟨t,_,rfl⟩
  have hst : s ≠ t := by
    intro he
    subst t
    exact hne rfl
  have hi : ∃ i, s i ≠ t i := by
    by_contra! he
    exact hst (funext he)
  obtain ⟨i,hi⟩ := hi
  rw [satisfies_fullClause_iff]
  refine ⟨i, ?_⟩
  cases hs : s i <;> cases ht : t i <;> simp_all

def MinimallyUnsatisfiable {α : Type*} [DecidableEq α]
    (F : Finset (Clause α)) : Prop :=
  Unsatisfiable F ∧ ∀ C ∈ F, ∃ a : α → Bool,
    ∀ D ∈ F.erase C, SatisfiesClause a D

theorem fullFormula_minimallyUnsatisfiable (n : ℕ) :
    MinimallyUnsatisfiable (fullFormula n) := by
  exact ⟨fullFormula_unsatisfiable n, fun _ h => fullFormula_erase_satisfiable h⟩

def NonTautological {α : Type*} (C : Clause α) : Prop :=
  ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)

lemma fullClause_nonTautological {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → Bool) : NonTautological (fullClause s) := by
  intro i
  simp only [mem_fullClause_iff]
  rintro ⟨ht,hf⟩
  simp_all

lemma fullFormula_nonTautological {n : ℕ} {C : Clause (Fin n)}
    (hC : C ∈ fullFormula n) : NonTautological C := by
  rcases Finset.mem_image.mp hC with ⟨s,_,rfl⟩
  exact fullClause_nonTautological s

end Kunisky
