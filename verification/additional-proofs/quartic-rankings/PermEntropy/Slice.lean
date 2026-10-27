import PermEntropy.TwoPoint
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic

/-!
# Exponential moments of fixed-cardinality binary words

For a word containing exactly `r` true symbols, `wordCrossing` is the
number of false-before-true pairs minus true-before-false pairs. This file
bounds the unnormalized exponential partition function, including empty
and impossible slices.
-/

open scoped BigOperators

namespace PermEntropy

def wordCount {q : ℕ} (w : Fin q → Bool) : ℕ :=
  ∑ i, if w i then 1 else 0

noncomputable def wordPosition {q : ℕ} (w : Fin q → Bool) : ℝ :=
  ∑ i, ((i.val : ℝ) + 1) * (if w i then 1 else 0)

noncomputable def wordCrossing {q : ℕ} (w : Fin q → Bool) : ℝ :=
  2 * wordPosition w - (wordCount w : ℝ) * ((q : ℝ) + 1)

noncomputable def fixedWordPartition (q r : ℕ) (t : ℝ) : ℝ :=
  ∑ w : Fin q → Bool, if wordCount w = r then Real.exp (t * wordCrossing w) else 0

theorem wordCount_le {q : ℕ} (w : Fin q → Bool) : wordCount w ≤ q := by
  calc
    wordCount w ≤ ∑ _i : Fin q, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      split <;> omega
    _ = q := by simp

theorem wordCount_zero_iff {q : ℕ} (w : Fin q → Bool) :
    wordCount w = 0 ↔ w = fun _ => false := by
  constructor
  · intro h
    funext i
    have hi : (if w i then 1 else 0) ≤ wordCount w :=
      Finset.single_le_sum (f := fun j => if w j then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hi
    cases hw : w i <;> simp_all
  · intro h
    simp [h, wordCount]

@[simp] theorem wordCount_false (q : ℕ) :
    wordCount (fun _ : Fin q => false) = 0 := by simp [wordCount]

@[simp] theorem wordCrossing_false (q : ℕ) :
    wordCrossing (fun _ : Fin q => false) = 0 := by
  simp [wordCrossing, wordPosition]

@[simp] theorem wordCount_cons {q : ℕ} (b : Bool) (w : Fin q → Bool) :
    wordCount (Fin.cons b w) = (if b then 1 else 0) + wordCount w := by
  unfold wordCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem sum_real_word_indicator {q : ℕ} (w : Fin q → Bool) :
    (∑ i, if w i then (1 : ℝ) else 0) = (wordCount w : ℝ) := by
  simp [wordCount, Nat.cast_sum]

theorem wordPosition_cons {q : ℕ} (b : Bool) (w : Fin q → Bool) :
    wordPosition (Fin.cons b w) =
      (if b then 1 else 0) + wordPosition w + (wordCount w : ℝ) := by
  unfold wordPosition
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, Nat.cast_zero, zero_add, one_mul,
    Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  rw [← sum_real_word_indicator]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  split <;> ring

theorem wordCrossing_cons_false {q : ℕ} (w : Fin q → Bool) :
    wordCrossing (Fin.cons false w) = wordCrossing w + (wordCount w : ℝ) := by
  simp only [wordCrossing, wordPosition_cons, wordCount_cons, Bool.false_eq_true,
    ↓reduceIte, zero_add, Nat.cast_add, Nat.cast_one]
  ring

theorem wordCrossing_cons_true {q : ℕ} (w : Fin q → Bool) :
    wordCrossing (Fin.cons true w) =
      wordCrossing w + (wordCount w : ℝ) - (q : ℝ) := by
  simp only [wordCrossing, wordPosition_cons, wordCount_cons, ↓reduceIte,
    Nat.cast_add, Nat.cast_one]
  ring

theorem sum_binary_words_succ (q : ℕ) (f : (Fin (q + 1) → Bool) → ℝ) :
    (∑ w, f w) = (∑ w : Fin q → Bool, f (Fin.cons false w)) +
      ∑ w : Fin q → Bool, f (Fin.cons true w) := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (q + 1) => Bool))
    (fun x : Bool × (Fin q → Bool) => f (Fin.cons x.1 x.2)) f (by intro x; rfl)
  rw [← h, Fintype.sum_prod_type, Fintype.sum_bool]
  exact add_comm _ _

@[simp] theorem fixedWordPartition_zero (q : ℕ) (t : ℝ) :
    fixedWordPartition q 0 t = 1 := by
  unfold fixedWordPartition
  rw [Finset.sum_eq_single (fun _ : Fin q => false)]
  · simp
  · intro w hw hne
    have hn : wordCount w ≠ 0 := by simpa [wordCount_zero_iff] using hne
    simp [hn]
  · simp

theorem fixedWordPartition_eq_zero {q r : ℕ} (hqr : q < r) (t : ℝ) :
    fixedWordPartition q r t = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  have hn : wordCount w ≠ r := by have := wordCount_le w; omega
  simp [hn]

theorem fixedWordPartition_nonneg (q r : ℕ) (t : ℝ) :
    0 ≤ fixedWordPartition q r t := by
  apply Finset.sum_nonneg
  intro w hw
  split <;> positivity

theorem fixedWordPartition_succ (q r : ℕ) (t : ℝ) :
    fixedWordPartition (q + 1) (r + 1) t =
      Real.exp (t * ((r : ℝ) + 1)) * fixedWordPartition q (r + 1) t +
      Real.exp (t * ((r : ℝ) - q)) * fixedWordPartition q r t := by
  unfold fixedWordPartition
  rw [sum_binary_words_succ]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    simp only [wordCount_cons, Bool.false_eq_true, ↓reduceIte, zero_add,
      wordCrossing_cons_false]
    by_cases h : wordCount w = r + 1
    · simp only [h, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp [h]
  · apply Finset.sum_congr rfl
    intro w hw
    simp only [wordCount_cons, ↓reduceIte, wordCrossing_cons_true]
    by_cases h : wordCount w = r
    · simp only [h, Nat.add_comm 1 r, ↓reduceIte]
      rw [← Real.exp_add]
      congr 1
      ring
    · have hh : 1 + wordCount w ≠ r + 1 := by omega
      simp [h, hh]

theorem choose_centering {q r : ℕ} (hr : r ≤ q) :
    (q.choose (r + 1) : ℝ) * ((r : ℝ) + 1) +
      (q.choose r : ℝ) * ((r : ℝ) - q) = 0 := by
  have h := Nat.choose_succ_right_eq q r
  have h' := congrArg (fun n : ℕ => (n : ℝ)) h
  push_cast [Nat.cast_sub hr] at h'
  nlinarith

theorem fixedWordPartition_le (q r : ℕ) (t : ℝ) :
    fixedWordPartition q r t ≤
      (q.choose r : ℝ) * Real.exp ((q : ℝ)^3 * t^2 / 2) := by
  induction q generalizing r with
  | zero =>
      cases r with
      | zero => simp
      | succ r =>
          rw [fixedWordPartition_eq_zero (by omega)]
          simp
  | succ q ih =>
      cases r with
      | zero =>
          simp only [fixedWordPartition_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
          exact Real.one_le_exp (by positivity)
      | succ r =>
          by_cases hr : r ≤ q
          · rw [fixedWordPartition_succ]
            have htwo := two_point_exp_le (q.choose (r + 1)) (q.choose r)
              ((r : ℝ) + 1) ((r : ℝ) - q) ((q : ℝ) + 1) t
              (by positivity) (by positivity) (by positivity)
              (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast Nat.succ_le_succ hr)
              (by rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hr))];
                  have : (0 : ℝ) ≤ r := by positivity
                  linarith)
              (choose_centering hr)
            have hcube : (q : ℝ)^3 + ((q : ℝ) + 1)^2 ≤ ((q : ℝ) + 1)^3 := by
              have hq : (0 : ℝ) ≤ q := by positivity
              nlinarith [sq_nonneg (q : ℝ)]
            calc
              _ ≤ Real.exp (t * ((r : ℝ) + 1)) *
                    ((q.choose (r + 1) : ℝ) * Real.exp ((q : ℝ)^3 * t^2 / 2)) +
                  Real.exp (t * ((r : ℝ) - q)) *
                    ((q.choose r : ℝ) * Real.exp ((q : ℝ)^3 * t^2 / 2)) :=
                add_le_add (mul_le_mul_of_nonneg_left (ih (r + 1)) (le_of_lt (Real.exp_pos _)))
                  (mul_le_mul_of_nonneg_left (ih r) (le_of_lt (Real.exp_pos _)))
              _ = ((q.choose (r + 1) : ℝ) * Real.exp (t * ((r : ℝ) + 1)) +
                    (q.choose r : ℝ) * Real.exp (t * ((r : ℝ) - q))) *
                    Real.exp ((q : ℝ)^3 * t^2 / 2) := by ring
              _ ≤ (((q.choose (r + 1) : ℝ) + (q.choose r : ℝ)) *
                    Real.exp (((q : ℝ) + 1)^2 * t^2 / 2)) *
                    Real.exp ((q : ℝ)^3 * t^2 / 2) :=
                mul_le_mul_of_nonneg_right htwo (le_of_lt (Real.exp_pos _))
              _ = ((q + 1).choose (r + 1) : ℝ) *
                    Real.exp ((((q : ℝ) + 1)^2 + (q : ℝ)^3) * t^2 / 2) := by
                rw [Nat.choose_succ_succ, Nat.cast_add]
                rw [mul_assoc, ← Real.exp_add]
                congr 1
                · ring
                · congr 1; ring
              _ ≤ _ := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Real.exp_le_exp.mpr
                simp only [Nat.cast_add, Nat.cast_one]
                nlinarith [mul_nonneg (sub_nonneg.mpr hcube) (sq_nonneg t)]
          · rw [fixedWordPartition_eq_zero (by omega), Nat.choose_eq_zero_of_lt (by omega)]
            simp

end PermEntropy
