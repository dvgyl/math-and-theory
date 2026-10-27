module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathAndTheory.Gyires

open Finset
open scoped BigOperators

/-- The dimension constant in Gyires's inequality. -/
noncomputable def dimensionConstant (n : ℕ) : ℝ := (n.factorial : ℝ) / (n : ℝ) ^ n

lemma factorial_mul_self_powers_le (m n : ℕ) :
    (m + n).factorial * (m ^ m * n ^ n) ≤
      (m.factorial * n.factorial) * (m + n) ^ (m + n) := by
  have hterm : m ^ m * n ^ n * (m + n).choose m ≤ (m + n) ^ (m + n) := by
    rw [add_pow]
    have h := Finset.single_le_sum
      (f := fun k => m ^ k * n ^ (m + n - k) * (m + n).choose k)
      (s := Finset.range (m + n + 1)) (fun k _ => Nat.zero_le _) (a := m)
      (by simp only [mem_range]; omega)
    simpa using h
  have hscaled := Nat.mul_le_mul_right (m.factorial * n.factorial) hterm
  have hfac : (m + n).choose m * m.factorial * n.factorial = (m + n).factorial := by
    simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
  calc
    (m + n).factorial * (m ^ m * n ^ n) =
        (m ^ m * n ^ n * (m + n).choose m) * (m.factorial * n.factorial) := by
          rw [← hfac]
          ring
    _ ≤ (m + n) ^ (m + n) * (m.factorial * n.factorial) := hscaled
    _ = (m.factorial * n.factorial) * (m + n) ^ (m + n) := Nat.mul_comm _ _

/-- Combining two positive dimensions decreases the dimension constant. -/
theorem dimensionConstant_add_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    dimensionConstant (m + n) ≤ dimensionConstant m * dimensionConstant n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (0 : ℝ) < (m + n : ℕ) := by exact_mod_cast (by omega : 0 < m + n)
  simp only [dimensionConstant, div_mul_div_comm]
  apply (div_le_div_iff₀ (pow_pos hsum _) (mul_pos (pow_pos hm' _) (pow_pos hn' _))).2
  exact_mod_cast factorial_mul_self_powers_le m n

lemma factorial_mul_self_powers_lt (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (m + n).factorial * (m ^ m * n ^ n) <
      (m.factorial * n.factorial) * (m + n) ^ (m + n) := by
  have hterm : m ^ m * n ^ n * (m + n).choose m < (m + n) ^ (m + n) := by
    rw [add_pow]
    let f := fun k => m ^ k * n ^ (m + n - k) * (m + n).choose k
    have hsubset : ({0, m} : Finset ℕ) ⊆ Finset.range (m + n + 1) := by
      intro k hk
      simp only [mem_insert, mem_singleton] at hk
      simp only [mem_range]
      omega
    have htwo := Finset.sum_le_sum_of_subset (f := f) hsubset
    have hne : (0 : ℕ) ≠ m := Nat.ne_of_lt hm
    simp only [Finset.sum_pair hne, f, pow_zero, Nat.sub_zero, Nat.choose_zero_right,
      one_mul, mul_one, Nat.add_sub_cancel_left] at htwo
    have hpos : 0 < n ^ (m + n) := Nat.pow_pos hn
    exact lt_of_lt_of_le (by omega) htwo
  have hscaled := Nat.mul_lt_mul_of_pos_right hterm
    (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos n))
  have hfac : (m + n).choose m * m.factorial * n.factorial = (m + n).factorial := by
    simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
  calc
    (m + n).factorial * (m ^ m * n ^ n) =
        (m ^ m * n ^ n * (m + n).choose m) * (m.factorial * n.factorial) := by
          rw [← hfac]
          ring
    _ < (m + n) ^ (m + n) * (m.factorial * n.factorial) := hscaled
    _ = (m.factorial * n.factorial) * (m + n) ^ (m + n) := Nat.mul_comm _ _

/-- Combining two positive dimensions strictly decreases the dimension constant. -/
theorem dimensionConstant_add_lt (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    dimensionConstant (m + n) < dimensionConstant m * dimensionConstant n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (0 : ℝ) < (m + n : ℕ) := by exact_mod_cast (by omega : 0 < m + n)
  simp only [dimensionConstant, div_mul_div_comm]
  apply (div_lt_div_iff₀ (pow_pos hsum _) (mul_pos (pow_pos hm' _) (pow_pos hn' _))).2
  exact_mod_cast factorial_mul_self_powers_lt m n hm hn

lemma dimensionConstant_nonneg (n : ℕ) : 0 ≤ dimensionConstant n := by
  unfold dimensionConstant
  positivity

/-- The dimension constant of a sum is bounded by the product of the block constants. -/
theorem dimensionConstant_sum_le (dims : List ℕ) (hpos : ∀ n ∈ dims, 0 < n) :
    dimensionConstant dims.sum ≤ (dims.map dimensionConstant).prod := by
  induction dims with
  | nil => norm_num [dimensionConstant]
  | cons a dims ih =>
    cases dims with
    | nil => simp
    | cons b rest =>
      have ha : 0 < a := hpos a (by simp)
      have hb : 0 < b := hpos b (by simp)
      have htail : 0 < (b :: rest).sum := by simp; omega
      have ht := ih (fun n hn => hpos n (List.mem_cons_of_mem a hn))
      simp only [List.sum_cons, List.map_cons, List.prod_cons] at ht ⊢
      exact (dimensionConstant_add_le a (b + rest.sum) ha htail).trans
        (mul_le_mul_of_nonneg_left ht (dimensionConstant_nonneg a))

/-- At least two positive blocks give a strict comparison of dimension constants. -/
theorem dimensionConstant_sum_lt (a b : ℕ) (rest : List ℕ)
    (hpos : ∀ n ∈ a :: b :: rest, 0 < n) :
    dimensionConstant (a :: b :: rest).sum <
      ((a :: b :: rest).map dimensionConstant).prod := by
  have ha : 0 < a := hpos a (by simp)
  have hb : 0 < b := hpos b (by simp)
  have htail : 0 < (b :: rest).sum := by simp; omega
  have ht := dimensionConstant_sum_le (b :: rest)
    (fun n hn => hpos n (List.mem_cons_of_mem a hn))
  simp only [List.sum_cons, List.map_cons, List.prod_cons] at ht ⊢
  exact (dimensionConstant_add_lt a (b + rest.sum) ha htail).trans_le
    (mul_le_mul_of_nonneg_left ht (dimensionConstant_nonneg a))

end MathAndTheory.Gyires
