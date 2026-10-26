module

public import Std

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace MathAndTheory.Hofstadter

@[expose] def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

/-- The recursive value, packaged together with the bound that makes every
recursive call in the defining iterate strictly smaller than its input. -/
@[expose] def boundedF (k : Nat) (n : Nat) : {a : Nat // a ≤ n} :=
  match n with
  | 0 => ⟨0, Nat.le_refl 0⟩
  | m + 1 =>
    let g : Fin (m + 1) → Fin (m + 1) := fun x =>
      let y := boundedF k x.val
      ⟨y.val, Nat.lt_of_le_of_lt y.property x.isLt⟩
    let z := iter g k ⟨m, Nat.lt_succ_self m⟩
    ⟨m + 1 - z.val, Nat.sub_le _ _⟩
termination_by n
decreasing_by exact x.isLt

@[expose] def F (k n : Nat) : Nat := (boundedF k n).val

theorem F_le (k n : Nat) : F k n ≤ n := (boundedF k n).property

theorem F_zero (k : Nat) : F k 0 = 0 := by
  simp [F, boundedF]

theorem iter_fin_val {b : Nat} (f : Nat → Nat)
    (hf : ∀ i, f i ≤ i) (t : Nat) (x : Fin b) :
    (iter (fun y : Fin b =>
      (⟨f y.val, Nat.lt_of_le_of_lt (hf _) y.isLt⟩ : Fin b)) t x).val =
      iter f t x.val := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [iter]; exact congrArg f ih

theorem F_succ (k n : Nat) :
    F k (n + 1) = n + 1 - iter (F k) k n := by
  simp only [F, boundedF]
  simpa only [F] using congrArg (fun z => n + 1 - z)
    (iter_fin_val (F k) (F_le k) k ⟨n, Nat.lt_succ_self n⟩)

theorem iter_le (f : Nat → Nat) (hf : ∀ i, f i ≤ i) (t n : Nat) :
    iter f t n ≤ n := by
  induction t with
  | zero => exact Nat.le_refl n
  | succ t ih => exact Nat.le_trans (hf _) ih

theorem iter_congr_bounded (f g : Nat → Nat) (hf : ∀ i, f i ≤ i)
    (n : Nat) (h : ∀ m, m ≤ n → f m = g m) (t : Nat) :
    iter f t n = iter g t n := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact (h _ (iter_le f hf t n)).trans (congrArg g ih)

/-- A finite table is a certificate only after each entry has been checked
against the actual defining recurrence. -/
@[expose] def tableValue (xs : List Nat) (n : Nat) : Nat := xs[n]?.getD 0

@[expose] def ValidTable (k : Nat) (xs : List Nat) : Prop :=
  ∀ i : Fin xs.length,
    tableValue xs i.val =
      if i.val = 0 then 0 else
        i.val - iter (tableValue xs) k (i.val - 1)

theorem validTable_correct (k : Nat) (xs : List Nat)
    (h : ValidTable k xs) (n : Nat) (hn : n < xs.length) :
    F k n = tableValue xs n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      have hz := h ⟨0, hn⟩
      simpa [F_zero] using hz.symm
    | succ n =>
      have hs := h ⟨n + 1, hn⟩
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel] at hs
      rw [F_succ, hs]
      apply congrArg (fun z => n + 1 - z)
      apply iter_congr_bounded (F k) (tableValue xs) (F_le k)
      intro m hm
      exact ih m (Nat.lt_succ_of_le hm)
        (Nat.lt_trans (Nat.lt_succ_of_le hm) hn)

@[expose] def table4 : List Nat :=
  [0, 1, 1, 2, 3, 4, 5, 5, 6, 6, 7, 8, 8, 9, 10, 11, 11, 12, 13, 14, 15, 15, 16, 17, 18, 19, 19, 20, 20, 21, 22, 23, 24, 24, 25, 25, 26, 27, 27, 28, 29, 30, 31, 31, 32, 32, 33, 34, 34, 35, 36, 37, 37, 38, 39, 40, 41, 41, 42, 42, 43, 44, 44, 45, 46, 47, 47, 48, 49, 50, 51, 51, 52, 53, 54, 55, 55, 56, 56, 57, 58, 58, 59, 60, 61, 61, 62, 63, 64, 65, 65, 66, 67, 68, 69, 69, 70, 70, 71, 72, 73, 74, 74, 75, 75, 76, 77, 77, 78, 79, 80, 80, 81, 82, 83, 84, 84, 85, 86, 87, 88, 88, 89, 89, 90, 91, 92, 93, 93, 94, 94, 95, 96]

theorem table4_valid : ValidTable 4 table4 := by unfold ValidTable; decide

theorem table4_correct (n : Nat) (hn : n ≤ 132) :
    F 4 n = tableValue table4 n := by
  apply validTable_correct 4 table4 table4_valid n
  have hlen : table4.length = 133 := by decide
  rw [hlen]
  omega

@[expose] def table5 : List Nat :=
  [0, 1, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 11, 12, 12, 13, 14, 15, 16, 16, 17, 18, 19, 20, 21, 21, 22, 23, 24, 25, 26, 26, 27, 27, 28, 29, 30, 31, 32, 32, 33, 33, 34, 35, 35, 36, 37, 38, 39, 40, 40, 41, 41, 42, 43, 43, 44, 45, 46, 46, 47, 48, 49, 50, 51, 51, 52, 52, 53, 54, 54, 55, 56, 57, 57, 58, 59, 60, 61, 61, 62, 63, 64, 65, 66, 66, 67, 67, 68, 69, 69, 70, 71, 72, 72, 73, 74, 75, 76, 76, 77, 78, 79, 80, 81, 81, 82, 83, 84, 85, 86, 86, 87, 87, 88, 89, 89, 90, 91, 92, 92, 93, 94, 95, 96, 96, 97, 98, 99, 100]

theorem table5_valid : ValidTable 5 table5 := by unfold ValidTable; decide

theorem table5_correct (n : Nat) (hn : n ≤ 132) :
    F 5 n = tableValue table5 n := by
  apply validTable_correct 5 table5 table5_valid n
  have hlen : table5.length = 133 := by decide
  rw [hlen]
  omega

theorem counterexample_left : iter (F 4) 9 132 = 8 := by
  calc
    iter (F 4) 9 132 = iter (tableValue table4) 9 132 :=
      iter_congr_bounded (F 4) (tableValue table4) (F_le 4) 132
        table4_correct 9
    _ = 8 := by decide

theorem counterexample_right : iter (F 5) 10 132 = 7 := by
  calc
    iter (F 5) 10 132 = iter (tableValue table5) 10 132 :=
      iter_congr_bounded (F 5) (tableValue table5) (F_le 5) 132
        table5_correct 10
    _ = 7 := by decide

theorem reverse_witness_left : iter (F 4) 9 36 = 2 := by
  calc
    iter (F 4) 9 36 = iter (tableValue table4) 9 36 :=
      iter_congr_bounded (F 4) (tableValue table4) (F_le 4) 36
        (fun n hn => table4_correct n (by omega)) 9
    _ = 2 := by decide

theorem reverse_witness_right : iter (F 5) 10 36 = 3 := by
  calc
    iter (F 5) 10 36 = iter (tableValue table5) 10 36 :=
      iter_congr_bounded (F 5) (tableValue table5) (F_le 5) 36
        (fun n hn => table5_correct n (by omega)) 10
    _ = 3 := by decide

/-- The first pair disproving the proposed late-iterate ordering is in fact
incomparable: either direction fails at an explicit natural-number input. -/
theorem pointwise_incomparable :
    (¬ ∀ n, iter (F 4) 9 n ≤ iter (F 5) 10 n) ∧
    (¬ ∀ n, iter (F 5) 10 n ≤ iter (F 4) 9 n) := by
  constructor
  · intro h
    have hbad := h 132
    rw [counterexample_left, counterexample_right] at hbad
    omega
  · intro h
    have hbad := h 36
    rw [reverse_witness_left, reverse_witness_right] at hbad
    omega

/-- The full pointwise-order conjecture stated in Section 7 of
Letouzey--Li--Steiner, JIS 29 (2026), Article 26.3.3:
for k ≥ 1 and j > 2k, F_k^j ≤ F_(k+1)^(j+1). -/
@[expose] def LateIterateOrderConjecture : Prop :=
  ∀ k j n : Nat, 1 ≤ k → 2 * k < j →
    iter (F k) j n ≤ iter (F (k + 1)) (j + 1) n

theorem lateIterateOrderConjecture_false : ¬ LateIterateOrderConjecture := by
  intro h
  have hbad := h 4 9 132 (by decide) (by decide)
  change iter (F 4) 9 132 ≤ iter (F 5) 10 132 at hbad
  rw [counterexample_left, counterexample_right] at hbad
  omega

#print axioms F_succ
#print axioms validTable_correct
#print axioms table4_valid
#print axioms table5_valid
#print axioms pointwise_incomparable
#print axioms lateIterateOrderConjecture_false

end MathAndTheory.Hofstadter
