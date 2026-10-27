module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Derivative

/-!
This file proves the fixed-mean maximizer lemma and both adjacent-probability bounds.
The probability coefficients are finite sums of Bernoulli outcome weights.
The proof permits parameters equal to zero or one.
The next modules use these results to prove the central likelihood bound and the matrix contractions.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace MathAndTheory.Gyires.Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def count (b : ι → Bool) : ℕ := ∑ i, if b i then 1 else 0

def weight (p : ι → ℝ) (b : ι → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i

def expectation (f : ℕ → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ b : ι → Bool, weight p b * f (count b)

lemma weight_update_affine (p : ι → ℝ) (i : ι) (x : ℝ) (b : ι → Bool) :
    weight (Function.update p i x) b =
      (1 - x) * weight (Function.update p i 0) b +
        x * weight (Function.update p i 1) b := by
  unfold weight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have he (y : ℝ) :
      (∏ j ∈ Finset.univ.erase i, if b j then Function.update p i y j
        else 1 - Function.update p i y j) =
      ∏ j ∈ Finset.univ.erase i, if b j then p j else 1 - p j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp only [he, Function.update_self]
  cases b i <;> simp

lemma expectation_update_affine (f : ℕ → ℝ) (p : ι → ℝ) (i : ι) (x : ℝ) :
    expectation f (Function.update p i x) =
      (1 - x) * expectation f (Function.update p i 0) +
        x * expectation f (Function.update p i 1) := by
  simp only [expectation, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [weight_update_affine]
  ring

omit [DecidableEq ι] in
lemma count_comp (b : ι → Bool) (σ : Equiv.Perm ι) : count (b ∘ σ) = count b := by
  exact Equiv.sum_comp σ (fun i => if b i then 1 else 0)

omit [DecidableEq ι] in
lemma weight_comp (p : ι → ℝ) (b : ι → Bool) (σ : Equiv.Perm ι) :
    weight (p ∘ σ) (b ∘ σ) = weight p b := by
  exact Equiv.prod_comp σ (fun i => if b i then p i else 1 - p i)

lemma expectation_comp (f : ℕ → ℝ) (p : ι → ℝ) (σ : Equiv.Perm ι) :
    expectation f (p ∘ σ) = expectation f p := by
  unfold expectation
  rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl Bool))
    (fun b => weight (p ∘ σ) b * f (count b))]
  apply Finset.sum_congr rfl
  intro b hb
  change weight (p ∘ σ) (b ∘ σ) * f (count (b ∘ σ)) = _
  rw [weight_comp, count_comp]

lemma continuous_expectation (f : ℕ → ℝ) : Continuous (expectation (ι := ι) f) := by
  unfold expectation weight
  apply continuous_finsetSum
  intro b hb
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i hi
    by_cases h : b i = true <;> simp [h] <;> fun_prop
  · exact continuous_const

def setPair (p : ι → ℝ) (i j : ι) (x y : ℝ) : ι → ℝ :=
  Function.update (Function.update p i x) j y

omit [Fintype ι] in
lemma setPair_comm (p : ι → ℝ) {i j : ι} (hij : i ≠ j) (x y : ℝ) :
    setPair p i j x y = setPair p j i y x := by
  exact Function.update_comm hij x y p

omit [Fintype ι] in
lemma setPair_swap (p : ι → ℝ) {i j : ι} (hij : i ≠ j) (x y : ℝ) :
    setPair p i j x y ∘ Equiv.swap i j = setPair p i j y x := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [setPair, hij]
  by_cases hkj : k = j
  · subst k
    simp [setPair, hij]
  simp [setPair, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

lemma expectation_pair_symmetric (f : ℕ → ℝ) (p : ι → ℝ)
    {i j : ι} (hij : i ≠ j) (x y : ℝ) :
    expectation f (setPair p i j x y) = expectation f (setPair p i j y x) := by
  rw [← expectation_comp f (setPair p i j x y) (Equiv.swap i j)]
  rw [setPair_swap p hij]

lemma expectation_pair_formula (f : ℕ → ℝ) (p : ι → ℝ)
    {i j : ι} (hij : i ≠ j) (x y : ℝ) :
    expectation f (setPair p i j x y) =
      expectation f (setPair p i j 0 0) +
      (expectation f (setPair p i j 1 0) - expectation f (setPair p i j 0 0)) *
        (x + y) +
      (expectation f (setPair p i j 1 1) -
        2 * expectation f (setPair p i j 1 0) + expectation f (setPair p i j 0 0)) *
        x * y := by
  have hx (z : ℝ) : expectation f (setPair p i j x z) =
      (1 - x) * expectation f (setPair p i j 0 z) +
        x * expectation f (setPair p i j 1 z) := by
    simp only [setPair_comm p hij]
    exact expectation_update_affine f (Function.update p j z) i x
  change expectation f (Function.update (Function.update p i x) j y) = _
  rw [expectation_update_affine]
  change (1 - y) * expectation f (setPair p i j x 0) +
    y * expectation f (setPair p i j x 1) = _
  rw [hx, hx, expectation_pair_symmetric f p hij 0 1]
  ring

lemma sum_update_apply (φ : ℝ → ℝ) (p : ι → ℝ) (i : ι) (x : ℝ) :
    (∑ k, φ (Function.update p i x k)) = (∑ k, φ (p k)) + φ x - φ (p i) := by
  have heq : (fun k => φ (Function.update p i x k)) =
      Function.update (fun k => φ (p k)) i (φ x) := Function.comp_update φ p i x
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs := Finset.add_sum_erase Finset.univ (fun k => φ (p k)) (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  linarith

lemma sum_setPair_apply (φ : ℝ → ℝ) (p : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (x y : ℝ) :
    (∑ k, φ (setPair p i j x y k)) =
      (∑ k, φ (p k)) + φ x + φ y - φ (p i) - φ (p j) := by
  unfold setPair
  rw [sum_update_apply, sum_update_apply, Function.update_of_ne (Ne.symm hij)]
  ring

lemma coefficient_zero_of_pair_max {a b B C D : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hab : a ≠ b)
    (hmax : ∀ x y : ℝ, (0 ≤ x ∧ x ≤ 1) → (0 ≤ y ∧ y ≤ 1) →
      x + y = a + b →
      D + B * (x + y) + C * x * y ≤ D + B * (a + b) + C * a * b) :
    C = 0 := by
  have hC : C ≤ 0 := by
    by_contra hn
    have hp : 0 < C := lt_of_not_ge hn
    have hm := hmax ((a + b) / 2) ((a + b) / 2)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by ring)
    have hd := mul_pos hp (sq_pos_of_ne_zero (sub_ne_zero.mpr hab))
    nlinarith
  have hC' : 0 ≤ C := by
    by_contra hn
    have hp : C < 0 := lt_of_not_ge hn
    by_cases hs : a + b ≤ 1
    · have hm := hmax 0 (a + b) ⟨le_rfl, by norm_num⟩
        ⟨by linarith, hs⟩ (by ring)
      have hd := mul_neg_of_neg_of_pos hp (mul_pos ha.1 hb.1)
      nlinarith
    · have hm := hmax 1 (a + b - 1) ⟨by norm_num, le_rfl⟩
        ⟨by linarith, by linarith⟩ (by ring)
      have hd := mul_neg_of_neg_of_pos hp (mul_pos (by linarith : 0 < 1-a)
        (by linarith : 0 < 1-b))
      nlinarith
  exact le_antisymm hC hC'

def parameters (μ : ℝ) : Set (ι → ℝ) :=
  Set.Icc 0 1 ∩ {p | ∑ i, p i = μ}

omit [DecidableEq ι] in
lemma isCompact_parameters (μ : ℝ) : IsCompact (parameters (ι := ι) μ) := by
  apply isCompact_Icc.inter_right
  exact isClosed_eq (by fun_prop) continuous_const

omit [Fintype ι] in
lemma setPair_self (p : ι → ℝ) (i j : ι) : setPair p i j (p i) (p j) = p := by
  simp [setPair]

lemma setPair_mem_parameters {μ : ℝ} {p : ι → ℝ} (hp : p ∈ parameters μ)
    {i j : ι} (hij : i ≠ j) {x y : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hxy : x + y = p i + p j) : setPair p i j x y ∈ parameters μ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k
    by_cases hkj : k = j
    · subst k
      simpa [setPair] using hy.1
    by_cases hki : k = i
    · subst k
      simpa [setPair, hkj] using hx.1
    simpa [setPair, hkj, hki] using hp.1.1 k
  · intro k
    by_cases hkj : k = j
    · subst k
      simpa [setPair] using hy.2
    by_cases hki : k = i
    · subst k
      simpa [setPair, hkj] using hx.2
    simpa [setPair, hkj, hki] using hp.1.2 k
  · change (∑ k, id (setPair p i j x y k)) = μ
    rw [sum_setPair_apply id p hij]
    simp only [id_eq]
    have hsum : (∑ k, p k) = μ := hp.2
    linarith

lemma exists_pair_spread {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) :
    ∃ x y : ℝ, (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
      x + y = a + b ∧ a ^ 2 + b ^ 2 < x ^ 2 + y ^ 2 := by
  by_cases hs : a + b ≤ 1
  · refine ⟨0, a + b, ⟨le_rfl, by norm_num⟩, ⟨by linarith, hs⟩, by ring, ?_⟩
    nlinarith [mul_pos ha.1 hb.1]
  · refine ⟨1, a + b - 1, ⟨by norm_num, le_rfl⟩,
      ⟨by linarith, by linarith⟩, by ring, ?_⟩
    nlinarith [mul_pos (by linarith : 0 < 1-a) (by linarith : 0 < 1-b)]

lemma maximizer_interior_equal (f : ℕ → ℝ) {μ : ℝ} {p : ι → ℝ}
    (hp : p ∈ parameters μ)
    (hmax : ∀ (q : ι → ℝ), q ∈ parameters μ → expectation f q ≤ expectation f p)
    (hsquares : ∀ (q : ι → ℝ), q ∈ parameters μ → expectation f q = expectation f p →
      (∑ k, q k ^ 2) ≤ ∑ k, p k ^ 2) :
    ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j := by
  intro i j hi hj
  by_contra hne
  have hij : i ≠ j := fun h => hne (congrArg p h)
  let D := expectation f (setPair p i j 0 0)
  let B := expectation f (setPair p i j 1 0) - D
  let C := expectation f (setPair p i j 1 1) -
    2 * expectation f (setPair p i j 1 0) + D
  have hformula (x y : ℝ) : expectation f (setPair p i j x y) =
      D + B * (x + y) + C * x * y := expectation_pair_formula f p hij x y
  have hpformula : expectation f p = D + B * (p i + p j) + C * p i * p j := by
    simpa only [setPair_self] using hformula (p i) (p j)
  have hC : C = 0 := coefficient_zero_of_pair_max hi hj hne (by
    intro x y hx hy hxy
    have h := hmax (setPair p i j x y) (setPair_mem_parameters hp hij hx hy hxy)
    rwa [hformula, hpformula] at h)
  obtain ⟨x, y, hx, hy, hxy, hspread⟩ := exists_pair_spread hi hj
  have hq := setPair_mem_parameters hp hij hx hy hxy
  have heq : expectation f (setPair p i j x y) = expectation f p := by
    simp only [hformula, hpformula, hC, hxy, zero_mul]
  have hsq := hsquares (setPair p i j x y) hq heq
  rw [sum_setPair_apply (fun z => z ^ 2) p hij] at hsq
  linarith

theorem exists_fixed_mean_maximizer (f : ℕ → ℝ) (μ : ℝ)
    (hne : (parameters (ι := ι) μ).Nonempty) :
    ∃ (p : ι → ℝ), p ∈ parameters μ ∧
      (∀ (q : ι → ℝ), q ∈ parameters μ → expectation f q ≤ expectation f p) ∧
      ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j := by
  obtain ⟨p₀, hp₀, hmax₀⟩ := (isCompact_parameters μ).exists_isMaxOn hne
    (continuous_expectation f).continuousOn
  let S : Set (ι → ℝ) := parameters μ ∩ {p | expectation f p = expectation f p₀}
  have hcompact : IsCompact S := (isCompact_parameters μ).inter_right
    (isClosed_eq (continuous_expectation f) continuous_const)
  have hS : S.Nonempty := ⟨p₀, hp₀, rfl⟩
  obtain ⟨p, hp, hsq⟩ := hcompact.exists_isMaxOn hS
    (show Continuous (fun p : ι → ℝ => ∑ k, p k ^ 2) by fun_prop).continuousOn
  have hmax : ∀ (q : ι → ℝ), q ∈ parameters μ → expectation f q ≤ expectation f p := by
    intro q hq
    rw [hp.2]
    exact hmax₀ hq
  refine ⟨p, hp.1, hmax, maximizer_interior_equal f hp.1 hmax ?_⟩
  intro q hq heq
  exact hsq ⟨hq, heq.trans hp.2⟩

omit [DecidableEq ι] in
lemma count_le_card (b : ι → Bool) : count b ≤ Fintype.card ι := by
  unfold count
  calc
    (∑ i, if b i then 1 else 0) ≤ ∑ _i : ι, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases b i <;> simp
    _ = Fintype.card ι := by simp

lemma sum_weight (p : ι → ℝ) : (∑ b : ι → Bool, weight p b) = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1 - p i)]
  simp

omit [DecidableEq ι] in
lemma weight_nonneg {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1) (b : ι → Bool) :
    0 ≤ weight p b := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact hp.1 i
  · exact sub_nonneg.mpr (hp.2 i)

def probability (p : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ b : ι → Bool, if count b = k then weight p b else 0

lemma probability_nonneg {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1) (k : ℕ) :
    0 ≤ probability p k := by
  apply Finset.sum_nonneg
  intro b hb
  split_ifs
  · exact weight_nonneg hp b
  · exact le_rfl

lemma sum_probability (p : ι → ℝ) :
    (∑ k ∈ Finset.range (Fintype.card ι + 1), probability p k) = 1 := by
  unfold probability
  rw [Finset.sum_comm]
  have heq (b : ι → Bool) :
      (∑ k ∈ Finset.range (Fintype.card ι + 1),
        if count b = k then weight p b else 0) = weight p b := by
    simp [Finset.sum_ite_eq, Nat.lt_succ_of_le (count_le_card b)]
  simp_rw [heq]
  exact sum_weight p

lemma expectation_eq_sum_probability (f : ℕ → ℝ) (p : ι → ℝ) :
    expectation f p =
      ∑ k ∈ Finset.range (Fintype.card ι + 1), probability p k * f k := by
  unfold probability expectation
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  simp [ite_mul, Finset.sum_ite_eq, Nat.lt_succ_of_le (count_le_card b)]

open Polynomial

noncomputable def generating (p : ι → ℝ) : Polynomial ℝ :=
  ∏ i, (C (1 - p i) + C (p i) * X)

lemma generating_eq_sum (p : ι → ℝ) :
    generating p = ∑ b : ι → Bool, C (weight p b) * X ^ count b := by
  let g (i : ι) (b : Bool) : Polynomial ℝ := if b then C (p i) * X else C (1 - p i)
  have hsum (i : ι) : C (1 - p i) + C (p i) * X = ∑ b : Bool, g i b := by
    simp [g, add_comm]
  unfold generating
  simp_rw [hsum]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have heq (i : ι) : g i (b i) =
      C (if b i then p i else 1 - p i) * X ^ (if b i then 1 else 0 : ℕ) := by
    cases b i <;> simp [g]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  rfl

lemma generating_coeff (p : ι → ℝ) (k : ℕ) :
    (generating p).coeff k = probability p k := by
  rw [generating_eq_sum]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, probability, eq_comm]

noncomputable def ones (p : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => p i = 1)

noncomputable def fractional (p : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < p i ∧ p i < 1)

lemma profile_counts_le (p : ι → ℝ) :
    (ones p).card + (fractional p).card ≤ Fintype.card ι := by
  classical
  have hd : Disjoint (ones p) (fractional p) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [ones, fractional, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact (ne_of_lt hj.2) hi
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_card (Finset.subset_univ _)

lemma generating_of_equal_interior {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1) (q : ℝ)
    (hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = q) :
    generating p = X ^ (ones p).card * (C (1-q) + C q * X) ^ (fractional p).card := by
  classical
  have heq (i : ι) : C (1 - p i) + C (p i) * X =
      (if i ∈ ones p then X else 1) *
        (if i ∈ fractional p then C (1-q) + C q * X else 1) := by
    by_cases h1 : p i = 1
    · simp [ones, fractional, h1]
    by_cases hfrac : 0 < p i ∧ p i < 1
    · simp only [ones, fractional, Finset.mem_filter, Finset.mem_univ, true_and,
        h1, hfrac, ite_false, ite_true, one_mul]
      rw [hconst i hfrac]
    · have h0 : p i = 0 := by
        have hpi0 : (0 : ℝ) ≤ p i := hp.1 i
        have hpi1 : p i ≤ (1 : ℝ) := hp.2 i
        rcases not_and_or.mp hfrac with h | h
        · linarith
        · exact False.elim (h1 (le_antisymm hpi1 (not_lt.mp h)))
      simp [ones, fractional, h0]
  unfold generating
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp

lemma sum_of_equal_interior {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1) (q : ℝ)
    (hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = q) :
    (∑ i, p i) = (ones p).card + (fractional p).card * q := by
  classical
  have heq (i : ι) : p i = (if i ∈ ones p then 1 else 0) +
      (if i ∈ fractional p then q else 0) := by
    by_cases h1 : p i = 1
    · simp [ones, fractional, h1]
    by_cases hfrac : 0 < p i ∧ p i < 1
    · simp only [ones, fractional, Finset.mem_filter, Finset.mem_univ, true_and,
        h1, hfrac, ite_false, ite_true, zero_add]
      exact hconst i hfrac
    · have h0 : p i = 0 := by
        have hpi0 : (0 : ℝ) ≤ p i := hp.1 i
        have hpi1 : p i ≤ (1 : ℝ) := hp.2 i
        rcases not_and_or.mp hfrac with h | h
        · linarith
        · exact False.elim (h1 (le_antisymm hpi1 (not_lt.mp h)))
      simp [ones, fractional, h0]
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  simp

theorem exists_fixed_mean_binomial_maximizer (f : ℕ → ℝ) (μ : ℝ)
    (hne : (parameters (ι := ι) μ).Nonempty) :
    ∃ (p : ι → ℝ) (a b : ℕ) (q : ℝ),
      p ∈ parameters μ ∧
      (∀ (v : ι → ℝ), v ∈ parameters μ → expectation f v ≤ expectation f p) ∧
      (0 < q ∧ q < 1) ∧ a + b ≤ Fintype.card ι ∧
      μ = a + b * q ∧ generating p = X ^ a * (C (1-q) + C q * X) ^ b := by
  obtain ⟨p, hp, hmax, hequal⟩ := exists_fixed_mean_maximizer f μ hne
  have hq : ∃ q : ℝ, (0 < q ∧ q < 1) ∧
      ∀ i, (0 < p i ∧ p i < 1) → p i = q := by
    by_cases h : ∃ i, 0 < p i ∧ p i < 1
    · obtain ⟨i, hi⟩ := h
      exact ⟨p i, hi, fun j hj => hequal j i hj hi⟩
    · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
      intro i hi
      exact False.elim (h ⟨i, hi⟩)
  obtain ⟨q, hq, hconst⟩ := hq
  refine ⟨p, (ones p).card, (fractional p).card, q, hp, hmax, hq,
    profile_counts_le p, ?_, generating_of_equal_interior hp.1 q hconst⟩
  have hsum : (∑ i, p i) = μ := hp.2
  rw [← hsum]
  exact sum_of_equal_interior hp.1 q hconst

lemma mul_derivative_pow (P : Polynomial ℝ) (n : ℕ) :
    P * derivative (P ^ n) = C (n : ℝ) * derivative P * P ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow_succ, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

noncomputable def shiftedBinomial (a b : ℕ) (q : ℝ) : Polynomial ℝ :=
  X ^ a * (C (1-q) + C q * X) ^ b

lemma shiftedBinomial_differential (a b : ℕ) (q : ℝ) :
    X * (C (1-q) + C q * X) * derivative (shiftedBinomial a b q) =
      (C ((a : ℝ) * (1-q)) + C (((a : ℝ) + b) * q) * X) *
        shiftedBinomial a b q := by
  let L : Polynomial ℝ := C (1-q) + C q * X
  have hX : X * derivative (X ^ a : Polynomial ℝ) = C (a : ℝ) * X ^ a := by
    simpa using mul_derivative_pow (X : Polynomial ℝ) a
  have hL : L * derivative (L ^ b) = C (b : ℝ) * C q * L ^ b := by
    simpa [L] using mul_derivative_pow L b
  change X * L * derivative (X ^ a * L ^ b) = _
  rw [derivative_mul]
  calc
    X * L * (derivative (X ^ a) * L ^ b + X ^ a * derivative (L ^ b)) =
        L * (X * derivative (X ^ a)) * L ^ b +
          X * X ^ a * (L * derivative (L ^ b)) := by ring
    _ = L * (C (a : ℝ) * X ^ a) * L ^ b +
          X * X ^ a * (C (b : ℝ) * C q * L ^ b) := by rw [hX, hL]
    _ = (C ((a : ℝ) * (1-q)) + C (((a : ℝ) + b) * q) * X) *
        shiftedBinomial a b q := by
      simp only [shiftedBinomial, L, map_mul, map_add]
      ring

lemma coeff_X_mul_derivative (P : Polynomial ℝ) (k : ℕ) :
    (X * derivative P).coeff k = (k : ℝ) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

lemma shiftedBinomial_coefficient_relation (a b m : ℕ) (q : ℝ) :
    (((m : ℝ) + 1) - a) * (1-q) * (shiftedBinomial a b q).coeff (m+1) =
      (((a : ℝ) + b) - m) * q * (shiftedBinomial a b q).coeff m := by
  have h := congrArg (fun P : Polynomial ℝ => P.coeff (m+1))
    (shiftedBinomial_differential a b q)
  have hpoly (P : Polynomial ℝ) :
      X * (C (1-q) + C q * X) * derivative P =
        C (1-q) * (X * derivative P) + C q * (X * (X * derivative P)) := by ring
  rw [hpoly, add_mul] at h
  simp only [coeff_add, coeff_C_mul, coeff_X_mul_derivative,
    coeff_X_mul, coeff_derivative, mul_assoc] at h
  nlinarith

lemma shiftedBinomial_central_upper_relation (a b m : ℕ) (q : ℝ)
    (hq : q < 1) (hmean : (m : ℝ) = a + b * q) :
    (((m : ℝ) + 1) - a) * (shiftedBinomial a b q).coeff (m+1) =
      ((m : ℝ) - a) * (shiftedBinomial a b q).coeff m := by
  have h := shiftedBinomial_coefficient_relation a b m q
  have hcoef : (((a : ℝ) + b) - m) * q = ((m : ℝ) - a) * (1-q) := by
    rw [hmean]
    ring
  rw [hcoef] at h
  have heq : (1-q) * ((((m : ℝ) + 1) - a) * (shiftedBinomial a b q).coeff (m+1)) =
      (1-q) * (((m : ℝ) - a) * (shiftedBinomial a b q).coeff m) := by nlinarith [h]
  exact mul_left_cancel₀ (by linarith : 1-q ≠ 0) heq

lemma upper_bound_of_central_relation {t a U V : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hV : 0 ≤ V)
    (hrel : (t+1) * U = t * V) :
    (t+a+1) * U ≤ (t+a) * V := by
  have hUV : U ≤ V := by
    apply (mul_le_mul_iff_right₀ (by linarith : 0 < t+1)).mp
    rw [hrel]
    exact mul_le_mul_of_nonneg_right (by linarith) hV
  have haux := mul_le_mul_of_nonneg_left hUV ha
  nlinarith

lemma probability_upper_of_profile {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1)
    (a b m : ℕ) (q : ℝ) (hq : 0 < q ∧ q < 1)
    (hmean : (m : ℝ) = a + b * q)
    (hpoly : generating p = shiftedBinomial a b q) :
    ((m : ℝ)+1) * probability p (m+1) ≤ (m : ℝ) * probability p m := by
  have hr := shiftedBinomial_central_upper_relation a b m q hq.2 hmean
  rw [← hpoly, generating_coeff, generating_coeff] at hr
  have ht : 0 ≤ (m : ℝ) - a := by
    rw [hmean]
    nlinarith [mul_nonneg (Nat.cast_nonneg b : (0:ℝ) ≤ b) hq.1.le]
  have h := upper_bound_of_central_relation ht (Nat.cast_nonneg a)
    (probability_nonneg hp m) (show ((m : ℝ) - a + 1) * probability p (m+1) =
      ((m : ℝ) - a) * probability p m by nlinarith [hr])
  convert h using 1 <;> congr 1 <;> ring

lemma expectation_linear (f g : ℕ → ℝ) (s t : ℝ) (p : ι → ℝ) :
    expectation (fun k => s * f k + t * g k) p =
      s * expectation f p + t * expectation g p := by
  simp only [expectation, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

lemma probability_eq_expectation (p : ι → ℝ) (k : ℕ) :
    probability p k = expectation (fun j => if j = k then 1 else 0) p := by
  simp only [probability, expectation, mul_ite, mul_one, mul_zero]

lemma expectation_probability_difference (p : ι → ℝ) (k l : ℕ) (s t : ℝ) :
    expectation (fun j => s * (if j = k then 1 else 0) -
      t * (if j = l then 1 else 0)) p =
      s * probability p k - t * probability p l := by
  simp only [sub_eq_add_neg, ← neg_mul]
  rw [expectation_linear, ← probability_eq_expectation, ← probability_eq_expectation]

/-- The upper adjacent-probability bound includes all boundary parameters. -/
theorem probability_adjacent_upper (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) :
    ((m : ℝ)+1) * probability p (m+1) ≤ (m : ℝ) * probability p m := by
  let f : ℕ → ℝ := fun j => ((m : ℝ)+1) * (if j = m+1 then 1 else 0) -
    (m : ℝ) * (if j = m then 1 else 0)
  obtain ⟨v, a, b, q, hv, hmax, hq, hab, hmean, hpoly⟩ :=
    exists_fixed_mean_binomial_maximizer f (m : ℝ) ⟨p, hp⟩
  have hvbound := probability_upper_of_profile hv.1 a b m q hq hmean hpoly
  have h := hmax p hp
  change expectation (fun j => ((m : ℝ)+1) * (if j = m+1 then 1 else 0) -
    (m : ℝ) * (if j = m then 1 else 0)) p ≤
    expectation (fun j => ((m : ℝ)+1) * (if j = m+1 then 1 else 0) -
    (m : ℝ) * (if j = m then 1 else 0)) v at h
  rw [expectation_probability_difference, expectation_probability_difference] at h
  linarith

omit [DecidableEq ι] in
lemma count_complement (b : ι → Bool) :
    count (fun i => !(b i)) + count b = Fintype.card ι := by
  unfold count
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i, ((if !(b i) then 1 else 0) + (if b i then 1 else 0))) =
        ∑ _i : ι, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      cases b i <;> simp
    _ = Fintype.card ι := by simp

omit [DecidableEq ι] in
lemma weight_complement (p : ι → ℝ) (b : ι → Bool) :
    weight (fun i => 1 - p i) (fun i => !(b i)) = weight p b := by
  unfold weight
  apply Finset.prod_congr rfl
  intro i hi
  cases h : b i <;> simp [h]

lemma probability_complement (p : ι → ℝ) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    probability (fun i => 1 - p i) (Fintype.card ι - k) = probability p k := by
  unfold probability
  let e : Equiv.Perm (ι → Bool) :=
    { toFun := fun b i => !(b i)
      invFun := fun b i => !(b i)
      left_inv := by intro b; funext i; simp
      right_inv := by intro b; funext i; simp }
  rw [← Equiv.sum_comp e
    (fun b : ι → Bool => if count b = Fintype.card ι - k then
      weight (fun i => 1 - p i) b else 0)]
  apply Finset.sum_congr rfl
  intro b hb
  change (if count (fun i => !(b i)) = Fintype.card ι - k then
    weight (fun i => 1 - p i) (fun i => !(b i)) else 0) = _
  rw [weight_complement]
  have hc := count_complement b
  have heq : count (fun i => !(b i)) = Fintype.card ι - k ↔ count b = k := by omega
  simp only [heq]

omit [DecidableEq ι] in
lemma mean_le_card {p : ι → ℝ} {m : ℕ} (hp : p ∈ parameters (m : ℝ)) :
    m ≤ Fintype.card ι := by
  have hsum : (∑ i, p i) = (m : ℝ) := hp.2
  have h : (m : ℝ) ≤ Fintype.card ι := by
    calc
      (m : ℝ) = ∑ i, p i := hsum.symm
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i hi => hp.1.2 i)
      _ = Fintype.card ι := by simp
  exact_mod_cast h

omit [DecidableEq ι] in
lemma complement_mem_parameters {p : ι → ℝ} {m : ℕ}
    (hp : p ∈ parameters (m : ℝ)) :
    (fun i => 1 - p i) ∈ parameters (Fintype.card ι - m : ℕ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    exact sub_nonneg.mpr (hp.1.2 i)
  · intro i
    have hi : (0 : ℝ) ≤ p i := hp.1.1 i
    change 1 - p i ≤ 1
    linarith
  · change (∑ i, (1 - p i)) = ((Fintype.card ι - m : ℕ) : ℝ)
    rw [Finset.sum_sub_distrib, Nat.cast_sub (mean_le_card hp)]
    have hsum : (∑ i, p i) = (m : ℝ) := hp.2
    simp [hsum]

/-- The lower adjacent-probability bound includes all boundary parameters. -/
theorem probability_adjacent_lower (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 1 ≤ m) :
    ((Fintype.card ι : ℝ) - m + 1) * probability p (m-1) ≤
      ((Fintype.card ι : ℝ) - m) * probability p m := by
  have hmn := mean_le_card hp
  have h := probability_adjacent_upper (fun i => 1 - p i) (Fintype.card ι - m)
    (complement_mem_parameters hp)
  have heq : Fintype.card ι - m + 1 = Fintype.card ι - (m-1) := by omega
  rw [heq, probability_complement p (m-1) (by omega), probability_complement p m hmn,
    Nat.cast_sub hmn] at h
  exact h

omit [DecidableEq ι] in
lemma generating_eval_one (p : ι → ℝ) : (generating p).eval 1 = 1 := by
  simp [generating, Polynomial.eval_prod]

lemma expectation_count_eq_sum_parameters (p : ι → ℝ) :
    expectation (fun k => (k : ℝ)) p = ∑ i, p i := by
  have h1 : (derivative (generating p)).eval 1 = expectation (fun k => (k : ℝ)) p := by
    rw [generating_eq_sum]
    simp [Polynomial.eval_finsetSum, Polynomial.derivative_X_pow, expectation]
  have h2 : (derivative (generating p)).eval 1 = ∑ i, p i := by
    unfold generating
    rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
    simp [Polynomial.eval_prod]
  exact h1.symm.trans h2

/-- Both adjacent inequalities hold for a Bernoulli sum with an integer mean. -/
theorem poissonBinomial_adjacent (p : ι → ℝ) (m : ℕ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hmean : (∑ i, p i) = (m : ℝ))
    (hm : 1 ≤ m) :
    (((m : ℝ)+1) * probability p (m+1) ≤ (m : ℝ) * probability p m) ∧
    (((Fintype.card ι : ℝ) - m + 1) * probability p (m-1) ≤
      ((Fintype.card ι : ℝ) - m) * probability p m) := by
  have hmem : p ∈ parameters (m : ℝ) :=
    ⟨⟨fun i => (hp i).1, fun i => (hp i).2⟩, hmean⟩
  exact ⟨probability_adjacent_upper p m hmem, probability_adjacent_lower p m hmem hm⟩


end MathAndTheory.Gyires.Bernoulli
