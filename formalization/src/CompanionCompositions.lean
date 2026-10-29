module
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open scoped BigOperators
namespace PowerRank.Companion

abbrev Letter (k : ℕ) := Fin 3 ⊕ Fin k
abbrev Composition (k M : ℕ) := {b : Letter k → ℕ // ∑ i, b i = M}

instance compositionFintype (k M : ℕ) : Fintype (Composition k M) :=
  Fintype.ofEquiv (Sym (Letter k) M) (Sym.equivNatSumOfFintype (Letter k) M)

/-- A fixed proof for the literal indices in `Fin 3`. -/
instance instNeZeroThree : NeZero (3 : ℕ) := @Nat.instNeZeroSucc 2

abbrev NormalComposition (k d M : ℕ) := {b : Composition k M // b.1 (Sum.inl 1) < d}

theorem composition_card (k M : ℕ) :
    Fintype.card (Composition k M) = (M+k+2).choose (k+2) := by
  rw [← Fintype.card_congr (Sym.equivNatSumOfFintype (Letter k) M), Sym.card_sym_eq_choose]
  simp only [Fintype.card_sum, Fintype.card_fin]
  have he : 3+k+M-1 = M+(k+2) := by omega
  rw [he, Nat.choose_symm_add]
  simp [Nat.add_assoc]

def normalizeTuple {k : ℕ} (d : ℕ) (b : Letter k → ℕ) : Letter k → ℕ :=
  Sum.elim ![b (Sum.inl 0)+(d-1)*(b (Sum.inl 1)/d),
    b (Sum.inl 1)%d, b (Sum.inl 2)+b (Sum.inl 1)/d]
    (fun i => b (Sum.inr i))

theorem normalizeTuple_sum {k : ℕ} (d : ℕ) (hd : 0 < d) (b : Letter k → ℕ) :
    ∑ i, normalizeTuple d b i = ∑ i, b i := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, normalizeTuple]
  have hdiv := Nat.mod_add_div (b (Sum.inl 1)) d
  have hp : d-1+1=d := by omega
  have hpq := congrArg (fun x : ℕ => x*(b (Sum.inl 1)/d)) hp
  simp only [add_mul, one_mul] at hpq
  omega

def normalize {k M : ℕ} (d : ℕ) (hd : 0 < d) (b : Composition k M) :
    NormalComposition k d M :=
  ⟨⟨normalizeTuple d b.1, (normalizeTuple_sum d hd b.1).trans b.2⟩,
    by simpa [normalizeTuple] using Nat.mod_lt (b.1 (Sum.inl 1)) hd⟩

theorem normalizeTuple_eq_self {k : ℕ} (d : ℕ) (b : Letter k → ℕ)
    (hb : b (Sum.inl 1) < d) : normalizeTuple d b = b := by
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [normalizeTuple, Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb]
  | inr i => rfl

theorem normalize_normal {k d M : ℕ} (hd : 0 < d) (b : NormalComposition k d M) :
    normalize d hd b.1 = b := by
  apply Subtype.ext
  apply Subtype.ext
  exact normalizeTuple_eq_self d b.1.1 b.2

def addAtOne {k : ℕ} (d : ℕ) (b : Letter k → ℕ) : Letter k → ℕ :=
  Function.update b (Sum.inl 1) (b (Sum.inl 1)+d)

def subAtOne {k : ℕ} (d : ℕ) (b : Letter k → ℕ) : Letter k → ℕ :=
  Function.update b (Sum.inl 1) (b (Sum.inl 1)-d)

theorem addAtOne_sum {k : ℕ} (d : ℕ) (b : Letter k → ℕ) :
    ∑ i, addAtOne d b i = (∑ i, b i)+d := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, addAtOne]
  simp
  omega

theorem subAtOne_sum {k : ℕ} (d : ℕ) (b : Letter k → ℕ) (hb : d ≤ b (Sum.inl 1)) :
    (∑ i, subAtOne d b i)+d = ∑ i, b i := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, subAtOne]
  simp
  omega

def badCompositionEquiv (k d M : ℕ) (hdM : d ≤ M) :
    Composition k (M-d) ≃ {b : Composition k M // d ≤ b.1 (Sum.inl 1)} where
  toFun b := ⟨⟨addAtOne d b.1, by rw [addAtOne_sum, b.2, Nat.sub_add_cancel hdM]⟩,
    by simp [addAtOne]⟩
  invFun b := ⟨subAtOne d b.1.1, by
    have h := subAtOne_sum d b.1.1 b.2
    rw [b.1.2] at h
    omega⟩
  left_inv b := by
    apply Subtype.ext
    funext i
    by_cases hi : i = Sum.inl 1 <;> simp [subAtOne, addAtOne, hi]
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i = Sum.inl 1
    · subst i
      simp [subAtOne, addAtOne, Nat.sub_add_cancel b.2]
    · simp [subAtOne, addAtOne, hi]

theorem normalComposition_card (k d M : ℕ) :
    Fintype.card (NormalComposition k d M) = (M+k+2).choose (k+2) -
      if M < d then 0 else (M-d+k+2).choose (k+2) := by
  classical
  have hsplit := Fintype.card_subtype_compl (fun b : Composition k M => ¬b.1 (Sum.inl 1) < d)
  simp only [not_not] at hsplit
  by_cases hMd : M < d
  · have hempty : IsEmpty {b : Composition k M // ¬b.1 (Sum.inl 1) < d} := by
      constructor
      intro b
      have hb : b.1.1 (Sum.inl 1) ≤ M := by
        calc
          _ ≤ ∑ i, b.1.1 i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
          _ = M := b.1.2
      omega
    have hzero : Fintype.card {b : Composition k M // ¬b.1 (Sum.inl 1) < d} = 0 := by
      exact @Fintype.card_of_isEmpty _ _ hempty
    rw [hzero] at hsplit
    simpa [NormalComposition, hMd, composition_card] using hsplit
  · have hdM : d ≤ M := by omega
    have hbad : Fintype.card {b : Composition k M // ¬b.1 (Sum.inl 1) < d} =
        (M-d+k+2).choose (k+2) := by
      have he : {b : Composition k M // ¬b.1 (Sum.inl 1) < d} ≃
          {b : Composition k M // d ≤ b.1 (Sum.inl 1)} := Equiv.subtypeEquivRight (fun b => by omega)
      rw [Fintype.card_congr he, ← Fintype.card_congr (badCompositionEquiv k d M hdM), composition_card]
    rw [hbad] at hsplit
    simpa [NormalComposition, hMd, composition_card] using hsplit

#print axioms composition_card
#print axioms normalizeTuple_sum
#print axioms normalizeTuple_eq_self
#print axioms normalize_normal
#print axioms addAtOne_sum
#print axioms subAtOne_sum
#print axioms normalComposition_card
end PowerRank.Companion
