import PermEntropy.Slice
import Mathlib.Order.Interval.Finset.Fin

/-! # The crossing statistic as a signed pair count -/

open scoped BigOperators

namespace PermEntropy

def indexCompare {q : ℕ} (i j : Fin q) : ℝ :=
  if i < j then 1 else if j < i then -1 else 0

theorem indexCompare_eq_sub {q : ℕ} (i j : Fin q) :
    indexCompare i j = (if i < j then 1 else 0) - (if j < i then 1 else 0) := by
  by_cases h : i < j
  · have hn : ¬ j < i := not_lt_of_ge h.le
    simp [indexCompare, h, hn]
  · by_cases h' : j < i <;> simp [indexCompare, h, h']

theorem indexCompare_skew {q : ℕ} (i j : Fin q) :
    indexCompare i j = -indexCompare j i := by
  rw [indexCompare_eq_sub, indexCompare_eq_sub]
  ring

theorem sum_indexCompare {q : ℕ} (j : Fin q) :
    (∑ i : Fin q, indexCompare i j) = 2 * (j.val : ℝ) + 1 - q := by
  simp only [indexCompare_eq_sub, Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.filter_gt_eq_Iio, Finset.filter_lt_eq_Ioi, Fin.card_Iio, Fin.card_Ioi]
  have hq : 1 ≤ q := by have := j.is_lt; omega
  have hj : j.val ≤ q - 1 := by have := j.is_lt; omega
  rw [Nat.cast_sub hj, Nat.cast_sub hq, Nat.cast_one]
  ring

theorem wordCrossing_eq_indicator_position {q : ℕ} (w : Fin q → Bool) :
    wordCrossing w = ∑ j, if w j then 2 * (j.val : ℝ) + 1 - q else 0 := by
  unfold wordCrossing wordPosition
  rw [← sum_real_word_indicator]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split <;> ring

theorem same_word_crossing_zero {q : ℕ} (w : Fin q → Bool) :
    (∑ i : Fin q, ∑ j : Fin q,
      if w i = true ∧ w j = true then indexCompare i j else 0) = 0 := by
  let T := ∑ i : Fin q, ∑ j : Fin q,
    if w i = true ∧ w j = true then indexCompare i j else 0
  have hT : T = -T := by
    dsimp [T]
    conv_lhs => rw [Finset.sum_comm]
    simp_rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hwi : w i = true
    · by_cases hwj : w j = true
      · simpa only [hwi, hwj, and_self, ↓reduceIte] using indexCompare_skew j i
      · simp [hwj]
    · simp [hwi]
  dsimp [T] at hT
  linarith

theorem wordCrossing_eq_pair_sum {q : ℕ} (w : Fin q → Bool) :
    wordCrossing w = ∑ i : Fin q, ∑ j : Fin q,
      if w i = false ∧ w j = true then
        (if i < j then 1 else if j < i then -1 else 0) else 0 := by
  have hdecomp :
      (∑ i : Fin q, ∑ j : Fin q,
        if w i = false ∧ w j = true then indexCompare i j else 0) =
      (∑ i : Fin q, ∑ j : Fin q, if w j = true then indexCompare i j else 0) -
      ∑ i : Fin q, ∑ j : Fin q,
        if w i = true ∧ w j = true then indexCompare i j else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    cases hwi : w i <;> cases hwj : w j <;> simp [hwi, hwj]
  rw [same_word_crossing_zero, sub_zero] at hdecomp
  conv_rhs at hdecomp => rw [Finset.sum_comm]
  change wordCrossing w = ∑ i : Fin q, ∑ j : Fin q,
    if w i = false ∧ w j = true then indexCompare i j else 0
  rw [hdecomp, wordCrossing_eq_indicator_position]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hwj : w j = true
  · simp only [hwj, ↓reduceIte, sum_indexCompare]
  · simp [hwj]

end PermEntropy
