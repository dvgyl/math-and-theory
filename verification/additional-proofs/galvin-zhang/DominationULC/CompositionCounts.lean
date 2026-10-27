import DominationULC.Sequences
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.List.Forall2
import Mathlib.Data.Finset.Prod

open scoped BigOperators

namespace DominationULC

/-- Explicit finite enumeration of positive integer lists with given upper bounds. -/
def boundedLists : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | b :: bs => ((Finset.Icc 1 b) ×ˢ boundedLists bs).image (fun p => p.1 :: p.2)

theorem mem_boundedLists (bounds xs : List ℕ) :
    xs ∈ boundedLists bounds ↔ List.Forall₂ (fun x b => 1 ≤ x ∧ x ≤ b) xs bounds := by
  induction bounds generalizing xs with
  | nil => cases xs <;> simp [boundedLists]
  | cons b bs ih =>
    cases xs with
    | nil => simp [boundedLists]
    | cons x xs => simp [boundedLists, Finset.mem_product, ih, and_assoc]

theorem part_eq_nat_sum (b : ℕ) :
    part b = ∑ i ∈ Finset.Icc 1 b, Finsupp.single (i : ℤ) (1 : ℝ) := by
  classical
  unfold part
  symm
  apply Finset.sum_bij (fun (i : ℕ) (_ : i ∈ Finset.Icc 1 b) => (i : ℤ))
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i hi j hj hij
    exact_mod_cast hij
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    rfl

theorem gapSeq_eq_sum_boundedLists (bounds : List ℕ) :
    gapSeq bounds = ∑ xs ∈ boundedLists bounds, Finsupp.single (xs.sum : ℤ) (1 : ℝ) := by
  classical
  induction bounds with
  | nil => simp [gapSeq, boundedLists, AddMonoidAlgebra.one_def]
  | cons b bs ih =>
    have hinj : Function.Injective (fun p : ℕ × List ℕ => p.1 :: p.2) := by
      intro p q h
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp only [List.cons.injEq] at h
      exact Prod.ext h.1 h.2
    change part b * gapSeq bs = _
    rw [part_eq_nat_sum, ih, Finset.sum_mul]
    simp only [boundedLists, Finset.sum_image (fun p _ q _ h => hinj h),
      Finset.sum_product, Finset.mul_sum, List.sum_cons, Nat.cast_add,
      AddMonoidAlgebra.single_mul_single, one_mul]

theorem gapSeq_apply_eq_count (bounds : List ℕ) (N : ℕ) :
    gapSeq bounds (N : ℤ) =
      (((boundedLists bounds).filter (fun xs => xs.sum = N)).card : ℝ) := by
  classical
  rw [gapSeq_eq_sum_boundedLists]
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Int.natCast_inj]
  simp only [Finset.sum_boole]

noncomputable def boundedCompositionEquiv (N : ℕ) (bounds : List ℕ) :
    {c : Composition N // List.Forall₂ (· ≤ ·) c.blocks bounds} ≃
      {xs // xs ∈ (boundedLists bounds).filter (fun xs => xs.sum = N)} where
  toFun c := ⟨c.val.blocks, by
    rw [Finset.mem_filter]
    refine ⟨?_, c.val.blocks_sum⟩
    rw [mem_boundedLists, List.forall₂_and_left]
    exact ⟨fun x hx => c.val.one_le_blocks hx, c.property⟩⟩
  invFun xs := by
    have hmem := (Finset.mem_filter.mp xs.property).1
    have hsum := (Finset.mem_filter.mp xs.property).2
    rw [mem_boundedLists, List.forall₂_and_left] at hmem
    exact ⟨⟨xs.val, fun hx => hmem.1 _ hx, hsum⟩, hmem.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Composition.ext
    rfl
  right_inv xs := by
    apply Subtype.ext
    rfl

/-- The convolution coefficient is the genuine number of restricted
compositions, not merely a formal generating-function definition. -/
theorem boundedComposition_card (N : ℕ) (bounds : List ℕ) :
    (Fintype.card {c : Composition N // List.Forall₂ (· ≤ ·) c.blocks bounds} : ℝ) =
      gapSeq bounds (N : ℤ) := by
  classical
  rw [Fintype.card_congr (boundedCompositionEquiv N bounds), Fintype.card_coe,
    gapSeq_apply_eq_count]

end DominationULC
