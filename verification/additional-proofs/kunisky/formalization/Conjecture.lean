import Resolution

namespace Kunisky

/-- The coalesced-mass functional defined in this package. External source identity is unverified.
`Tree.mass t C` is the coalesced dyadic mass `2^(-d(C))` of clause C. -/
noncomputable def certificateValue {n : ℕ} (F : Finset (Clause (Fin n)))
    (t : Tree (Fin n)) : ℝ :=
  (1 + ∑ v : Fin n, Real.sqrt
    (∑ C ∈ F.filter (fun C => (v,true) ∈ C ∨ (v,false) ∈ C), t.mass C)) /
  (∑ C ∈ F, Real.sqrt (t.mass C))

/-- An internal universal-bound predicate. Every resolution proof is quantified.
The historical identifier does not authenticate any external conjecture. -/
def Conjecture44 : Prop :=
  ∀ (n : ℕ) (F : Finset (Clause (Fin n))) (t : Tree (Fin n)),
    Unsatisfiable F → t.Valid F → t.conclusion = ∅ →
    certificateValue F t < 1 + Real.sqrt 2

lemma mem_fullClause {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → Bool) (v : α) : (v,s v) ∈ fullClause s := by
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

lemma fullClause_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (fullClause : (α → Bool) → Clause α) := by
  intro a b hab
  funext i
  have h := mem_fullClause a i
  rw [hab] at h
  rcases Finset.mem_image.mp h with ⟨j,_,hj⟩
  have hji : j = i := congrArg Prod.fst hj
  subst j
  exact (congrArg Prod.snd hj).symm

lemma fullFormula_contains {n : ℕ} {C : Clause (Fin n)} (hC : C ∈ fullFormula n)
    (v : Fin n) : (v,true) ∈ C ∨ (v,false) ∈ C := by
  rcases Finset.mem_image.mp hC with ⟨s,_,rfl⟩
  have h := mem_fullClause s v
  cases hs : s v with
  | false => right; simpa [hs] using h
  | true => left; simpa [hs] using h

lemma fullFormula_filter (n : ℕ) (v : Fin n) :
    (fullFormula n).filter (fun C => (v,true) ∈ C ∨ (v,false) ∈ C) = fullFormula n := by
  apply Finset.filter_eq_self.mpr
  intro C hC
  exact fullFormula_contains hC v

lemma sum_fullFormula {n : ℕ} (f : Clause (Fin n) → ℝ) :
    (∑ C ∈ fullFormula n, f C) = ∑ s : Fin n → Bool, f (fullClause s) := by
  unfold fullFormula
  exact Finset.sum_image fun a _ b _ h => fullClause_injective h

lemma certificateValue_fullFormula {n : ℕ} {t : Tree (Fin n)}
    (h : t.Valid (fullFormula n)) :
    certificateValue (fullFormula n) t =
      ((n : ℝ) + 1) / (∑ s : Fin n → Bool, Real.sqrt (t.mass (fullClause s))) := by
  unfold certificateValue
  simp_rw [fullFormula_filter]
  rw [t.sum_mass h, sum_fullFormula]
  simp only [Real.sqrt_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  congr 1
  ring

end Kunisky
