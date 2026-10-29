import LeafMode.Graph
import LeafMode.Counting
import Mathlib.Algebra.Polynomial.Coeff

/-! The ordinary domination polynomial, and its exact relation to the branch enumeration.
Every term in `dominationPolynomial` is indexed by an actual vertex subset and
weighted by its actual cardinality. -/
noncomputable section
open scoped BigOperators
open Polynomial

namespace LeafMode

attribute [local instance] Classical.propDecidable

def Dominates {α : Type*} [DecidableEq α] (G : SimpleGraph α) (s : Finset α) : Prop :=
  ∀ x, x ∈ s ∨ ∃ y, y ∈ s ∧ G.Adj x y

def dominationPolynomial {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : Polynomial ℤ :=
  ∑ s : Finset α, if Dominates G s then X ^ s.card else 0

/-- The coefficient is the ordinary number of dominating vertex subsets of the
specified cardinality. -/
theorem coeff_dominationPolynomial {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (d : ℕ) :
    (dominationPolynomial G).coeff d =
      ((Finset.univ.filter (fun s : Finset α => Dominates G s ∧ s.card = d)).card : ℤ) := by
  classical
  simp only [dominationPolynomial, finset_sum_coeff]
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : Dominates G s
  · simp [h, coeff_X_pow, eq_comm]
  · simp [h]

namespace Semantics
open Counting V
attribute [local instance] Classical.propDecidable

abbrev Selection (n k l : ℕ) := Bool × (Fin n → Branch k) × (Fin l → Bool)

def selected {n k l : ℕ} (c : Selection n k l) : V n k l → Prop
  | root => c.1 = true
  | u i => (c.2.1 i).1 = true
  | v i => (c.2.1 i).2.1 = true
  | tip i j => j ∈ (c.2.1 i).2.2
  | extra j => c.2.2 j = true

def toSet {n k l : ℕ} (c : Selection n k l) : Finset (V n k l) :=
  Finset.univ.filter (selected c)

@[simp] theorem mem_toSet {n k l : ℕ} (c : Selection n k l) (x : V n k l) :
    x ∈ toSet c ↔ selected c x := by
  simp [toSet]

def fromSet {n k l : ℕ} (s : Finset (V n k l)) : Selection n k l :=
  (decide (root ∈ s),
    (fun i => (decide (u i ∈ s), decide (v i ∈ s),
      Finset.univ.filter (fun j => tip i j ∈ s))),
    (fun j => decide (extra j ∈ s)))

@[simp] theorem toSet_fromSet {n k l : ℕ} (s : Finset (V n k l)) :
    toSet (fromSet s) = s := by
  ext x
  cases x <;> simp [selected, fromSet]

@[simp] theorem fromSet_toSet {n k l : ℕ} (c : Selection n k l) :
    fromSet (toSet c) = c := by
  rcases c with ⟨r, b, e⟩
  apply Prod.ext
  · cases r <;> simp [fromSet, selected]
  apply Prod.ext
  · funext i
    apply Prod.ext
    · cases h : (b i).1 <;> simp [fromSet, selected, h]
    apply Prod.ext
    · cases h : (b i).2.1 <;> simp [fromSet, selected, h]
    · ext j
      simp [fromSet, selected]
  · funext j
    cases h : e j <;> simp [fromSet, selected, h]

def selectionEquiv (n k l : ℕ) : Selection n k l ≃ Finset (V n k l) where
  toFun := toSet
  invFun := fromSet
  left_inv := fromSet_toSet
  right_inv := toSet_fromSet

def vertexEquiv (n k l : ℕ) :
    V n k l ≃ Unit ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin k) ⊕ Fin l where
  toFun
    | root => Sum.inl ()
    | u i => Sum.inr (Sum.inl i)
    | v i => Sum.inr (Sum.inr (Sum.inl i))
    | tip i j => Sum.inr (Sum.inr (Sum.inr (Sum.inl (i,j))))
    | extra j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))
  invFun
    | Sum.inl _ => root
    | Sum.inr (Sum.inl i) => u i
    | Sum.inr (Sum.inr (Sum.inl i)) => v i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i,j)))) => tip i j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => extra j
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · cases x; rfl
    rcases x with x | x
    · rfl
    rcases x with x | x
    · rfl
    rcases x with x | x
    · rcases x with ⟨i,j⟩; rfl
    · rfl

theorem prod_vertices {n k l : ℕ} (f : V n k l → P) :
    (∏ x, f x) = f root * (∏ i, f (u i)) * (∏ i, f (v i)) *
      (∏ i, ∏ j, f (tip i j)) * (∏ j, f (extra j)) := by
  rw [← Equiv.prod_comp (vertexEquiv n k l).symm]
  simp [Fintype.prod_sum_type, Fintype.prod_prod_type, vertexEquiv, mul_assoc]

theorem set_weight {n k l : ℕ} (c : Selection n k l) :
    (X : P) ^ (toSet c).card =
      bitWeight c.1 * (∏ i, branchWeight (c.2.1 i)) *
        (∏ j, bitWeight (c.2.2 j)) := by
  have h : (X : P) ^ (toSet c).card =
      ∏ x : V n k l, if x ∈ toSet c then (X : P) else 1 := by
    rw [Fintype.prod_ite_mem]
    simp
  rw [h, prod_vertices]
  simp only [mem_toSet, selected, branchWeight, bitWeight, Finset.prod_mul_distrib]
  simp [Fintype.prod_ite_mem, mul_assoc]

theorem exists_vertex {n k l : ℕ} (p : V n k l → Prop) :
    (∃ x, p x) ↔ p root ∨ (∃ i, p (u i)) ∨ (∃ i, p (v i)) ∨
      (∃ i j, p (tip i j)) ∨ (∃ j, p (extra j)) := by
  constructor
  · rintro ⟨x,h⟩
    cases x with
    | root => exact Or.inl h
    | u i => exact Or.inr (Or.inl ⟨i,h⟩)
    | v i => exact Or.inr (Or.inr (Or.inl ⟨i,h⟩))
    | tip i j => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,j,h⟩)))
    | extra j => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j,h⟩)))
  · rintro (h | ⟨i,h⟩ | ⟨i,h⟩ | ⟨i,j,h⟩ | ⟨j,h⟩)
    · exact ⟨root,h⟩
    · exact ⟨u i,h⟩
    · exact ⟨v i,h⟩
    · exact ⟨tip i j,h⟩
    · exact ⟨extra j,h⟩

def covered {n k l : ℕ} (c : Selection n k l) (x : V n k l) : Prop :=
  selected c x ∨ ∃ y, selected c y ∧ (graph n k l).Adj x y

@[simp] theorem covered_root {n k l : ℕ} (c : Selection n k l) :
    covered c root ↔ c.1 = true ∨ (∃ i, (c.2.1 i).1 = true) ∨
      (∃ j, c.2.2 j = true) := by
  simp [covered, exists_vertex, selected, parent]

@[simp] theorem covered_u {n k l : ℕ} (c : Selection n k l) (i : Fin n) :
    covered c (u i) ↔ c.1 = true ∨ (c.2.1 i).1 = true ∨ (c.2.1 i).2.1 = true := by
  simp [covered, exists_vertex, selected, parent, or_comm, or_left_comm, or_assoc]

@[simp] theorem covered_v {n k l : ℕ} (c : Selection n k l) (i : Fin n) :
    covered c (v i) ↔ (c.2.1 i).2.1 = true ∨ (c.2.1 i).1 = true ∨
      (c.2.1 i).2.2.Nonempty := by
  simp [covered, exists_vertex, selected, parent, Finset.Nonempty]

@[simp] theorem covered_tip {n k l : ℕ} (c : Selection n k l) (i : Fin n) (j : Fin k) :
    covered c (tip i j) ↔ (c.2.1 i).2.1 = true ∨ j ∈ (c.2.1 i).2.2 := by
  simp [covered, exists_vertex, selected, parent, or_comm]

@[simp] theorem covered_extra {n k l : ℕ} (c : Selection n k l) (j : Fin l) :
    covered c (extra j) ↔ c.2.2 j = true ∨ c.1 = true := by
  simp [covered, exists_vertex, selected, parent]

def valid {n k l : ℕ} (c : Selection n k l) : Prop :=
  (∀ i, branchValid c.1 (c.2.1 i)) ∧
    (c.1 = true ∨ (∃ i, (c.2.1 i).1 = true) ∨ (∃ j, c.2.2 j = true)) ∧
    (∀ j, c.2.2 j = true ∨ c.1 = true)

theorem dominates_iff_valid {n k l : ℕ} (hk : 0 < k) (c : Selection n k l) :
    Dominates (graph n k l) (toSet c) ↔ valid c := by
  have hc : Dominates (graph n k l) (toSet c) ↔ ∀ x, covered c x := by
    simp [Dominates, covered]
  rw [hc]
  constructor
  · intro h
    refine ⟨?_, covered_root c |>.mp (h root), ?_⟩
    · intro i
      apply (branchValid_iff hk c.1 (c.2.1 i)).mpr
      exact ⟨fun j => (covered_tip c i j).mp (h (tip i j)),
        (covered_v c i).mp (h (v i)), (covered_u c i).mp (h (u i))⟩
    · intro j
      exact (covered_extra c j).mp (h (extra j))
  · rintro ⟨hb,hr,he⟩ x
    cases x with
    | root => exact (covered_root c).mpr hr
    | u i => exact (covered_u c i).mpr ((branchValid_iff hk c.1 (c.2.1 i)).mp (hb i)).2.2
    | v i => exact (covered_v c i).mpr ((branchValid_iff hk c.1 (c.2.1 i)).mp (hb i)).2.1
    | tip i j => exact (covered_tip c i j).mpr (((branchValid_iff hk c.1 (c.2.1 i)).mp (hb i)).1 j)
    | extra j => exact (covered_extra c j).mpr (he j)

def rootConfigEquiv (n k : ℕ) :
    (Bool × (Fin n → Branch k)) ≃ Finset (V n k 0) where
  toFun c := toSet (c.1, c.2, fun j => Fin.elim0 j)
  invFun s := ((fromSet s).1, (fromSet s).2.1)
  left_inv := by
    intro c
    simp only [fromSet_toSet]
  right_inv := by
    intro s
    have h : ((fromSet s).1, (fromSet s).2.1, fun j : Fin 0 => (Fin.elim0 j : Bool)) =
        fromSet s := by
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext j
      exact Fin.elim0 j
    change toSet ((fromSet s).1, (fromSet s).2.1,
      fun j : Fin 0 => (Fin.elim0 j : Bool)) = s
    rw [h, toSet_fromSet]

def extendedConfigEquiv (n k : ℕ) :
    (Bool × Bool × (Fin n → Branch k)) ≃ Finset (V n k 1) where
  toFun c := toSet (c.1, c.2.2, fun _ => c.2.1)
  invFun s := ((fromSet s).1, (fromSet s).2.2 0, (fromSet s).2.1)
  left_inv := by
    intro c
    simp only [fromSet_toSet]
  right_inv := by
    intro s
    have h : ((fromSet s).1, (fromSet s).2.1,
        fun _ : Fin 1 => (fromSet s).2.2 0) = fromSet s := by
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext j
      exact congrArg (fromSet s).2.2 (Subsingleton.elim 0 j)
    change toSet ((fromSet s).1, (fromSet s).2.1,
      fun _ : Fin 1 => (fromSet s).2.2 0) = s
    rw [h, toSet_fromSet]

theorem rootConfig_valid {n k : ℕ} (hk : 0 < k) (c : Bool × (Fin n → Branch k)) :
    Dominates (graph n k 0) (rootConfigEquiv n k c) ↔ rootValid c.1 c.2 := by
  change Dominates (graph n k 0) (toSet _) ↔ _
  rw [dominates_iff_valid hk]
  simp [valid, rootValid]

theorem extendedConfig_valid {n k : ℕ} (hk : 0 < k)
    (c : Bool × Bool × (Fin n → Branch k)) :
    Dominates (graph n k 1) (extendedConfigEquiv n k c) ↔
      extendedValid c.1 c.2.1 c.2.2 := by
  change Dominates (graph n k 1) (toSet _) ↔ _
  rw [dominates_iff_valid hk]
  simp [valid, extendedValid]

theorem rootConfig_weight {n k : ℕ} (c : Bool × (Fin n → Branch k)) :
    (X : P) ^ (rootConfigEquiv n k c).card =
      bitWeight c.1 * ∏ i, branchWeight (c.2 i) := by
  change (X : P) ^ (toSet _).card = _
  rw [set_weight]
  simp

theorem extendedConfig_weight {n k : ℕ}
    (c : Bool × Bool × (Fin n → Branch k)) :
    (X : P) ^ (extendedConfigEquiv n k c).card =
      bitWeight c.1 * bitWeight c.2.1 * ∏ i, branchWeight (c.2.2 i) := by
  change (X : P) ^ (toSet _).card = _
  rw [set_weight]
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem dominationPolynomial_root {n k : ℕ} (hk : 0 < k) :
    dominationPolynomial (graph n k 0) = rootGF n k := by
  classical
  symm
  unfold rootGF dominationPolynomial
  calc
    _ = ∑ c : Bool × (Fin n → Branch k),
        if rootValid c.1 c.2 then bitWeight c.1 * ∏ i, branchWeight (c.2 i) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (rootConfigEquiv n k)
      intro c
      rw [rootConfig_weight]
      by_cases h : rootValid c.1 c.2
      · simp [h, (rootConfig_valid hk c).mpr h]
      · have hn := not_congr (rootConfig_valid hk c)
        simp [h, hn.mpr h]

theorem dominationPolynomial_extended {n k : ℕ} (hk : 0 < k) :
    dominationPolynomial (graph n k 1) = extendedGF n k := by
  classical
  symm
  unfold extendedGF dominationPolynomial
  calc
    _ = ∑ c : Bool × Bool × (Fin n → Branch k),
        if extendedValid c.1 c.2.1 c.2.2 then
          bitWeight c.1 * bitWeight c.2.1 * ∏ i, branchWeight (c.2.2 i) else 0 := by
      simp only [Fintype.sum_prod_type]
    _ = _ := by
      apply Fintype.sum_equiv (extendedConfigEquiv n k)
      intro c
      rw [extendedConfig_weight]
      by_cases h : extendedValid c.1 c.2.1 c.2.2
      · simp [h, (extendedConfig_valid hk c).mpr h]
      · have hn := not_congr (extendedConfig_valid hk c)
        simp [h, hn.mpr h]

end Semantics
end LeafMode
