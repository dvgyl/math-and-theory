import Policy

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Kunisky

def partialClause {n : ℕ} (P N : Finset (Fin n)) : Clause (Fin n) :=
  P.image (fun i => (i,true)) ∪ N.image (fun i => (i,false))

theorem partial_full {n : ℕ} (P N : Finset (Fin n))
    (hd : Disjoint P N) (hu : P ∪ N = Finset.univ) :
    partialClause P N = fullClause (fun i => if i ∈ P then true else false) := by
  classical
  have hc (i : Fin n) : i ∈ P ∨ i ∈ N := by
    have : i ∈ P ∪ N := by rw [hu]; simp
    exact Finset.mem_union.mp this
  ext ⟨i,b⟩
  by_cases hp : i ∈ P
  · have hn : i ∉ N := fun hn => Finset.disjoint_left.mp hd hp hn
    cases b <;> simp [partialClause, fullClause, hp, hn]
  · have hn : i ∈ N := (hc i).resolve_left hp
    cases b <;> simp [partialClause, fullClause, hp, hn]

theorem partial_resolves {n : ℕ} (P N : Finset (Fin n)) (j : Fin n)
    (hp : j ∉ P) (hn : j ∉ N) :
    (partialClause (insert j P) N).erase (j,true) ∪
      (partialClause P (insert j N)).erase (j,false) = partialClause P N := by
  ext ⟨i,b⟩
  cases b <;> by_cases hij : i = j <;>
    simp_all [partialClause, Finset.mem_erase]

/-- Every consistent partial clause has a finite ordinary tree derivation from all full clauses. -/
theorem complete_exists {n : ℕ} (P N : Finset (Fin n)) (hd : Disjoint P N) :
    ∃ t : Tree (Fin n), t.Valid (fullFormula n) ∧ t.conclusion = partialClause P N := by
  classical
  generalize hk : (Finset.univ \ (P ∪ N)).card = k
  induction k using Nat.strong_induction_on generalizing P N with
  | h k ih =>
    by_cases hu : P ∪ N = Finset.univ
    · refine ⟨.leaf (partialClause P N), ?_, rfl⟩
      change partialClause P N ∈ fullFormula n
      rw [partial_full P N hd hu]
      simp [fullFormula]
    · have hjex : ∃ j : Fin n, j ∉ P ∧ j ∉ N := by
        by_contra he
        apply hu
        ext j
        simp only [Finset.mem_univ, iff_true, Finset.mem_union]
        by_contra hh
        exact he ⟨j, not_or.mp hh⟩
      obtain ⟨j,hjp,hjn⟩ := hjex
      have hdl : Disjoint (insert j P) N := by
        apply Finset.disjoint_left.mpr
        intro i hip hin
        rcases Finset.mem_insert.mp hip with rfl | hip
        · exact hjn hin
        · exact Finset.disjoint_left.mp hd hip hin
      have hdr : Disjoint P (insert j N) := by
        apply Finset.disjoint_left.mpr
        intro i hip hin
        rcases Finset.mem_insert.mp hin with rfl | hin
        · exact hjp hip
        · exact Finset.disjoint_left.mp hd hip hin
      have hmiss : j ∈ Finset.univ \ (P ∪ N) := by simp [hjp,hjn]
      have hsetl : Finset.univ \ (insert j P ∪ N) =
          (Finset.univ \ (P ∪ N)).erase j := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        tauto
      have hsetr : Finset.univ \ (P ∪ insert j N) =
          (Finset.univ \ (P ∪ N)).erase j := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        tauto
      have hkl : (Finset.univ \ (insert j P ∪ N)).card < k := by
        rw [hsetl, ← hk]
        exact Finset.card_erase_lt_of_mem hmiss
      have hkr : (Finset.univ \ (P ∪ insert j N)).card < k := by
        rw [hsetr, ← hk]
        exact Finset.card_erase_lt_of_mem hmiss
      obtain ⟨l,hl,hlc⟩ := ih _ hkl (insert j P) N hdl rfl
      obtain ⟨r,hr,hrc⟩ := ih _ hkr P (insert j N) hdr rfl
      refine ⟨.node j l r, ?_, ?_⟩
      · refine ⟨hl,hr,?_,?_⟩
        · rw [hlc]; simp [partialClause]
        · rw [hrc]; simp [partialClause]
      · simp only [Tree.conclusion, hlc, hrc]
        exact partial_resolves P N j hjp hjn

namespace PolicyState

noncomputable def complete {n : ℕ} (s : PolicyState n) : Tree (Fin n) :=
  Classical.choose (complete_exists s.pos s.neg s.disjoint)

theorem complete_valid {n : ℕ} (s : PolicyState n) :
    s.complete.Valid (fullFormula n) :=
  (Classical.choose_spec (complete_exists s.pos s.neg s.disjoint)).1

theorem complete_conclusion {n : ℕ} (s : PolicyState n) :
    s.complete.conclusion = s.clause :=
  (Classical.choose_spec (complete_exists s.pos s.neg s.disjoint)).2

theorem target_mem (n : ℕ) : (target n).clause ∈ fullFormula n := by
  rw [clause_target]
  simp [positiveClause, fullFormula]

end PolicyState
end Kunisky
