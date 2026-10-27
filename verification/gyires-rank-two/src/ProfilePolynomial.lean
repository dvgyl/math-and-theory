module

public import ConvexLawMaximizer
public import LawTransform

@[expose] public section

open scoped BigOperators
open Finset Polynomial

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma profile_parts_disjoint (p : ι → ℝ) : Disjoint (ones p) (fractional p) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [ones, fractional, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact (ne_of_lt hj.2) hi

lemma profile_zero_count (p : ι → ℝ) :
    ((univ : Finset ι) \ (ones p ∪ fractional p)).card =
      Fintype.card ι - (ones p).card - (fractional p).card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_union_of_disjoint (profile_parts_disjoint p), Nat.sub_sub]

theorem prod_of_equal_interior {R : Type*} [CommMonoid R] (f : ℝ → R)
    {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1) (q : ℝ)
    (hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = q) :
    (∏ i, f (p i)) = f 1 ^ (ones p).card * f q ^ (fractional p).card *
      f 0 ^ (Fintype.card ι - (ones p).card - (fractional p).card) := by
  classical
  have heq (i : ι) : f (p i) =
      (if i ∈ ones p then f 1 else 1) *
      (if i ∈ fractional p then f q else 1) *
      (if i ∈ ((univ : Finset ι) \ (ones p ∪ fractional p)) then f 0 else 1) := by
    by_cases h1 : p i = 1
    · simp [ones, fractional, h1]
    by_cases hfrac : 0 < p i ∧ p i < 1
    · simp only [ones, fractional, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, Finset.mem_union, h1, hfrac, false_or, not_true_eq_false,
        true_and, ite_false, ite_true, one_mul, mul_one]
      exact congrArg f (hconst i hfrac)
    · have h0 : p i = 0 := by
        have hpi0 : (0 : ℝ) ≤ p i := hp.1 i
        have hpi1 : p i ≤ (1 : ℝ) := hp.2 i
        rcases not_and_or.mp hfrac with h | h
        · linarith
        · exact False.elim (h1 (le_antisymm hpi1 (not_lt.mp h)))
      simp [ones, fractional, h0]
  simp_rw [heq]
  simp only [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_mem_eq, Finset.prod_const, profile_zero_count]

noncomputable def profilePolynomial (n a m : ℕ) (t : ℝ) : ℝ[X] :=
  (1 + C (1-t/n)*X)^a * (1 + C ((t-a)/m-t/n)*X)^m *
    (1 - C (t/n)*X)^(n-a-m)

theorem centered_generating_profile {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1)
    (q θ : ℝ) (hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = q) :
    elementaryGenerating (fun i => p i-θ) =
      (1+C (1-θ)*X)^(ones p).card * (1+C (q-θ)*X)^(fractional p).card *
        (1-C θ*X)^(Fintype.card ι-(ones p).card-(fractional p).card) := by
  unfold elementaryGenerating
  rw [prod_of_equal_interior (fun x => (1+C (x-θ)*X : ℝ[X])) hp q hconst]
  simp only [zero_sub, map_neg, neg_mul, ← sub_eq_add_neg]

theorem centered_generating_profile_positive {p : ι → ℝ} {t q : ℝ}
    (hp : p ∈ parameters t) (hm : 0 < (fractional p).card)
    (hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = q) :
    elementaryGenerating (fun i => p i-t/Fintype.card ι) =
      profilePolynomial (Fintype.card ι) (ones p).card (fractional p).card t := by
  have hsum := sum_of_equal_interior hp.1 q hconst
  rw [hp.2] at hsum
  have hm0 : ((fractional p).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hq : q = (t-(ones p).card)/(fractional p).card := by
    apply (eq_div_iff hm0).mpr
    linarith
  rw [centered_generating_profile hp.1 q _ hconst, hq]
  rfl

theorem sum_bernoulli_variance_profile {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1)
    (q : ℝ) (hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = q) :
    (∑ i, p i*(1-p i)) = (fractional p).card*q*(1-q) := by
  classical
  have heq (i : ι) : p i*(1-p i) =
      if i ∈ fractional p then q*(1-q) else 0 := by
    by_cases hfrac : 0 < p i ∧ p i < 1
    · have hmem : i ∈ fractional p := by
        simpa only [fractional, Finset.mem_filter, Finset.mem_univ, true_and] using hfrac
      simp only [hmem, ite_true]
      rw [hconst i hfrac]
    · have hbound : p i = 0 ∨ p i = 1 := by
        have h0 : 0 ≤ p i := hp.1 i
        have h1 : p i ≤ 1 := hp.2 i
        rcases not_and_or.mp hfrac with h | h
        · exact Or.inl (le_antisymm (not_lt.mp h) h0)
        · exact Or.inr (le_antisymm h1 (not_lt.mp h))
      rcases hbound with h | h <;> simp [h, fractional]
  simp_rw [heq]
  simp only [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]
  ring

theorem sum_bernoulli_variance_profile_positive {p : ι → ℝ} {t q : ℝ}
    (hp : p ∈ parameters t) (hm : 0 < (fractional p).card)
    (hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = q) :
    (∑ i, p i*(1-p i)) =
      (t-(ones p).card)*((fractional p).card+(ones p).card-t)/(fractional p).card := by
  have hsum := sum_of_equal_interior hp.1 q hconst
  rw [hp.2] at hsum
  have hm0 : ((fractional p).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hq : q = (t-(ones p).card)/(fractional p).card := by
    apply (eq_div_iff hm0).mpr
    linarith
  rw [sum_bernoulli_variance_profile hp.1 q hconst, hq]
  field_simp [hm0]
  ring

end MathAndTheory.Gyires.RankTwo
