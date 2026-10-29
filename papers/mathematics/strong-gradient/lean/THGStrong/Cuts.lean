import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
open Finset

namespace THGStrong

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def cutPrefix (u : ι → ℝ) (i : ι) : ℝ := ∑ k, if k ≤ i then u k else 0
def cutBefore (u : ι → ℝ) (i : ι) : ℝ := ∑ k, if k < i then u k else 0
def cutAfter (u : ι → ℝ) (i : ι) : ℝ := ∑ k, if i < k then u k else 0

def orderMask (i j : ι) : ℝ := if j < i then 1 else 0

def orderedWeight (u s v t : ι → ℝ) (i j : ι) : ℝ :=
  if i < j then u i * v j else if j < i then s j * t i else 0

omit [Fintype ι] in
lemma orderedWeight_self (u s v t : ι → ℝ) (i : ι) :
    orderedWeight u s v t i i = 0 := by simp [orderedWeight]

lemma cutPrefix_sub_before (u : ι → ℝ) (i : ι) :
    cutPrefix u i - cutBefore u i = u i := by
  unfold cutPrefix cutBefore
  rw [← sum_sub_distrib]
  have hpoint (k : ι) :
      (if k ≤ i then u k else 0) - (if k < i then u k else 0) =
        if k = i then u i else 0 := by
    rcases lt_trichotomy k i with h | h | h
    · simp [le_of_lt h, h, ne_of_lt h]
    · subst k; simp
    · simp [not_le_of_gt h, not_lt_of_ge (le_of_lt h), ne_of_gt h]
  simp_rw [hpoint]
  simp

lemma orderedWeight_row (u s v t : ι → ℝ) (i : ι) :
    (∑ j, orderedWeight u s v t i j) =
      u i * cutAfter v i + t i * cutBefore s i := by
  have hp (j : ι) : orderedWeight u s v t i j =
      u i * (if i < j then v j else 0) +
        t i * (if j < i then s j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [orderedWeight, h, not_lt_of_ge h.le]
    · subst j; simp [orderedWeight]
    · simp [orderedWeight, h, not_lt_of_ge h.le, mul_comm]
  simp_rw [hp]
  simp only [sum_add_distrib, ← mul_sum, cutAfter, cutBefore]

lemma orderedWeight_column (u s v t : ι → ℝ) (i : ι) :
    (∑ j, orderedWeight u s v t j i) =
      v i * cutBefore u i + s i * cutAfter t i := by
  have hp (j : ι) : orderedWeight u s v t j i =
      v i * (if j < i then u j else 0) +
        s i * (if i < j then t j else 0) := by
    rcases lt_trichotomy j i with h | h | h
    · simp [orderedWeight, h, not_lt_of_ge h.le, mul_comm]
    · subst j; simp [orderedWeight]
    · simp [orderedWeight, h, not_lt_of_ge h.le]
  simp_rw [hp]
  simp only [sum_add_distrib, ← mul_sum, cutAfter, cutBefore]

lemma orderedWeight_divergence (u s v t : ι → ℝ) (i : ι) :
    (∑ j, (orderedWeight u s v t i j - orderedWeight u s v t j i)) =
      u i * cutAfter v i + t i * cutBefore s i -
        v i * cutBefore u i - s i * cutAfter t i := by
  rw [sum_sub_distrib, orderedWeight_row, orderedWeight_column]
  ring

lemma orderedWeight_sum_both (u s v t : ι → ℝ) (i : ι) :
    (∑ j, (orderedWeight u s v t i j + orderedWeight u s v t j i)) =
      u i * cutAfter v i + t i * cutBefore s i +
        v i * cutBefore u i + s i * cutAfter t i := by
  rw [sum_add_distrib, orderedWeight_row, orderedWeight_column]
  ring

omit [Fintype ι] in
lemma orderedWeight_quadratic_point (u s v t : ι → ℝ)
    (i j k l : ι) (hij : i ≤ j) :
    orderedWeight u s v t k l * (orderMask k i - orderMask l i) *
      (orderMask k j - orderMask l j) =
    (if k ≤ i then u k else 0) * (if j < l then v l else 0) +
      (if l ≤ i then s l else 0) * (if j < k then t k else 0) := by
  by_cases hki : k ≤ i
  · have hnik : ¬ i < k := not_lt_of_ge hki
    have hnjk : ¬ j < k := not_lt_of_ge (le_trans hki hij)
    by_cases hjl : j < l
    · have hil : i < l := lt_of_le_of_lt hij hjl
      have hkl : k < l := lt_of_le_of_lt hki hil
      simp [orderedWeight, orderMask, hki, hnik, hnjk, hjl, hil, hkl]
    · simp [orderMask, hnjk, hjl]
  · have hik : i < k := lt_of_not_ge hki
    by_cases hli : l ≤ i
    · have hnil : ¬ i < l := not_lt_of_ge hli
      have hnjl : ¬ j < l := not_lt_of_ge (le_trans hli hij)
      by_cases hjk : j < k
      · have hlk : l < k := lt_of_le_of_lt hli hik
        simp [orderedWeight, orderMask, hki, hli, hik, hnil, hnjl, hjk,
          hlk, not_lt_of_ge hlk.le]
      · simp [orderMask, hjk, hnjl]
    · have hil : i < l := lt_of_not_ge hli
      simp [orderMask, hik, hil, hki, hli]

lemma orderedWeight_quadratic_cut (u s v t : ι → ℝ)
    (i j : ι) (hij : i ≤ j) :
    (∑ k, ∑ l, orderedWeight u s v t k l *
      (orderMask k i - orderMask l i) * (orderMask k j - orderMask l j)) =
      cutPrefix u i * cutAfter v j + cutPrefix s i * cutAfter t j := by
  simp_rw [orderedWeight_quadratic_point u s v t i j _ _ hij]
  simp only [sum_add_distrib]
  unfold cutPrefix cutAfter
  rw [sum_comm (f := fun k l =>
    (if l ≤ i then s l else 0) * (if j < k then t k else 0))]
  simp only [← mul_sum, ← sum_mul]

lemma orderedWeight_linear_after (u s v t : ι → ℝ) (μ : ℝ)
    (i j : ι) (hij : i ≤ j) :
    (∑ k, (orderedWeight u s v t k i + μ * orderedWeight u s v t i k) *
      (orderMask k j - orderMask i j)) =
      s i * cutAfter t j + μ * u i * cutAfter v j := by
  have hp (k : ι) :
      (orderedWeight u s v t k i + μ * orderedWeight u s v t i k) *
        (orderMask k j - orderMask i j) =
      s i * (if j < k then t k else 0) +
        μ*u i * (if j < k then v k else 0) := by
    have hnji : ¬ j < i := not_lt_of_ge hij
    by_cases hjk : j < k
    · have hik : i < k := lt_of_le_of_lt hij hjk
      simp [orderedWeight, orderMask, hjk, hik, hnji, not_lt_of_ge hik.le]
      ring
    · simp [orderMask, hnji, hjk]
  simp_rw [hp]
  simp only [sum_add_distrib, ← mul_sum, cutAfter]

lemma orderedWeight_linear_before (u s v t : ι → ℝ) (μ : ℝ)
    (i j : ι) (hij : i < j) :
    (∑ k, (orderedWeight u s v t k j + μ * orderedWeight u s v t j k) *
      (orderMask k i - orderMask j i)) =
      -(cutPrefix u i * v j + μ * cutPrefix s i * t j) := by
  have hp (k : ι) :
      (orderedWeight u s v t k j + μ * orderedWeight u s v t j k) *
        (orderMask k i - orderMask j i) =
      -((if k ≤ i then u k else 0) * v j +
        μ * (if k ≤ i then s k else 0) * t j) := by
    by_cases hki : k ≤ i
    · have hkj : k < j := lt_of_le_of_lt hki hij
      simp [orderedWeight, orderMask, hki, hij, hkj,
        not_lt_of_ge hki, not_lt_of_ge hkj.le]
      ring
    · have hik : i < k := lt_of_not_ge hki
      simp [orderMask, hij, hki, hik]
  simp_rw [hp]
  simp only [sum_neg_distrib, sum_add_distrib, ← sum_mul, ← mul_sum, cutPrefix]

#print axioms orderedWeight_quadratic_cut
#print axioms orderedWeight_linear_after
#print axioms orderedWeight_linear_before

end THGStrong
