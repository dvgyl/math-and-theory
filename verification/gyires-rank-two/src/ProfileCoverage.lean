module

public import ProfilePolynomial

@[expose] public section

open scoped BigOperators
open Polynomial

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_centered_profile {p : ι → ℝ} {t : ℝ}
    (hp : p ∈ parameters t) (ht : 0 < t ∧ t < Fintype.card ι)
    (hequal : ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j) :
    ∃ a m : ℕ, 0 < m ∧ a+m ≤ Fintype.card ι ∧
      ((a : ℝ) < t ∧ t < a+m ∨ t = a ∧ m = 1) ∧
      elementaryGenerating (fun i => p i-t/Fintype.card ι) =
        profilePolynomial (Fintype.card ι) a m t ∧
      (∑ i, p i*(1-p i)) = (t-a)*((m : ℝ)+a-t)/m := by
  by_cases hfrac : ∃ i, 0 < p i ∧ p i < 1
  · obtain ⟨i, hi⟩ := hfrac
    have hm : 0 < (fractional p).card := Finset.card_pos.mpr ⟨i, by
      simpa only [fractional, Finset.mem_filter, Finset.mem_univ, true_and] using hi⟩
    have hconst : ∀ j, (0 < p j ∧ p j < 1) → p j = p i :=
      fun j hj => hequal j i hj hi
    have hsum := sum_of_equal_interior hp.1 (p i) hconst
    rw [hp.2] at hsum
    have hmreal : (0 : ℝ) < (fractional p).card := by exact_mod_cast hm
    refine ⟨(ones p).card, (fractional p).card, hm, profile_counts_le p,
      Or.inl ⟨?_, ?_⟩, centered_generating_profile_positive hp hm hconst,
      sum_bernoulli_variance_profile_positive hp hm hconst⟩
    · nlinarith
    · nlinarith
  · have hm : (fractional p).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hfrac ⟨i, by simpa only [fractional, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi⟩
    have hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = 0 :=
      fun i hi => False.elim (hfrac ⟨i, hi⟩)
    have hsum := sum_of_equal_interior hp.1 0 hconst
    rw [hp.2, hm] at hsum
    simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
    have ha : (ones p).card < Fintype.card ι := by
      have har : ((ones p).card : ℝ) < Fintype.card ι := by
        rw [← hsum]
        exact ht.2
      exact_mod_cast har
    refine ⟨(ones p).card, 1, by decide, Nat.succ_le_iff.mpr ha,
      Or.inr ⟨hsum, rfl⟩, ?_, ?_⟩
    · rw [centered_generating_profile hp.1 0 _ hconst, hm]
      simp only [pow_zero, mul_one, Nat.sub_zero, zero_sub, map_neg, neg_mul,
        ← sub_eq_add_neg]
      unfold profilePolynomial
      rw [hsum]
      simp only [sub_self, Nat.cast_one, zero_div, zero_sub, map_neg, neg_mul,
        ← sub_eq_add_neg, pow_one]
      have hexp : Fintype.card ι-(ones p).card =
          1+(Fintype.card ι-(ones p).card-1) := by omega
      rw [hexp, pow_add, pow_one]
      simp only [Nat.add_sub_cancel_left]
      ring
    · rw [sum_bernoulli_variance_profile hp.1 0 hconst]
      simp [hsum]

theorem profile_intervals_overlap (a m c l : ℕ) (t : ℝ)
    (hm : 0 < m) (hl : 0 < l)
    (hp : (a : ℝ) < t ∧ t < a+m ∨ t = a ∧ m = 1)
    (hq : (c : ℝ) < t ∧ t < c+l ∨ t = c ∧ l = 1) :
    max a c < min (a+m) (c+l) ∧
      ((max a c : ℕ) : ℝ) ≤ t ∧ t ≤ ((min (a+m) (c+l) : ℕ) : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hleft : (a : ℝ) ≤ t ∧ (c : ℝ) ≤ t := by
    constructor
    · rcases hp with hp | hp <;> linarith
    · rcases hq with hq | hq <;> linarith
  have hright : t < (a : ℝ)+m ∧ t < (c : ℝ)+l := by
    constructor
    · rcases hp with hp | hp <;> linarith
    · rcases hq with hq | hq <;> linarith
  have hcross : a < c+l ∧ c < a+m := by
    constructor
    · exact_mod_cast (by linarith : (a : ℝ) < c+l)
    · exact_mod_cast (by linarith : (c : ℝ) < a+m)
  constructor
  · exact max_lt (lt_min (Nat.lt_add_of_pos_right hm) hcross.1)
      (lt_min hcross.2 (Nat.lt_add_of_pos_right hl))
  · simp only [Nat.cast_max, Nat.cast_min, Nat.cast_add]
    exact ⟨max_le hleft.1 hleft.2, le_min hright.1.le hright.2.le⟩

end MathAndTheory.Gyires.RankTwo
