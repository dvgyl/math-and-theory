module

public import MathAndTheory.Mathematics.Gyires.BernoulliMaximizer
public import Mathlib.Tactic.FieldSimp

/-!
This file proves the central likelihood bound for a Bernoulli sum with an integer mean.
It also proves the squared likelihood norm bound and the equality case of the central lower bound.
The proof uses the fixed-mean maximizer and a coefficient recurrence for shifted binomial laws.
Deterministic laws can attain the norm bound. Its full equality classification is not proved here.
-/

@[expose] public section

open scoped BigOperators
open Finset Polynomial

namespace MathAndTheory.Gyires.Bernoulli

lemma profile_tail_ratio_le {a b n m j q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ n)
    (hm : 0 < m) (hmn : m < n) (hmj : m ≤ j) (hjn : j < n)
    (hq : 0 < q ∧ q < 1) (hmean : m = a + b*q) :
    q * (a+b-j) / ((1-q) * (j+1-a)) ≤
      (n-j) * m / ((j+1) * (n-m)) := by
  have ham : a ≤ m := by rw [hmean]; nlinarith [mul_nonneg hb hq.1.le]
  have hmab : m ≤ a+b := by rw [hmean]; nlinarith [mul_nonneg hb (sub_nonneg.mpr hq.2.le)]
  have hnm : 0 < n-m := by linarith
  have hnj : 0 < n-j := by linarith
  have hma : 0 < m+1-a := by linarith
  have hja : 0 < j+1-a := by linarith
  have hj1 : 0 < j+1 := by linarith
  have hq1 : 0 < 1-q := by linarith
  let K := q * (n-m) / ((1-q)*m)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hq.1.le hnm.le) (mul_nonneg hq1.le hm.le)
  have hA : (a+b-j)/(n-j) ≤ (a+b-m)/(n-m) := by
    apply (div_le_div_iff₀ hnj hnm).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hmj) (sub_nonneg.mpr hab)]
  have hD : (j+1)/(j+1-a) ≤ (m+1)/(m+1-a) := by
    apply (div_le_div_iff₀ hja hma).mpr
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hmj)]
  have hprod : (a+b-j)/(n-j) * ((j+1)/(j+1-a)) ≤
      (a+b-m)/(n-m) * ((m+1)/(m+1-a)) := by
    exact mul_le_mul hA hD (div_nonneg hj1.le hja.le)
      (div_nonneg (sub_nonneg.mpr hmab) hnm.le)
  have hcentral : K * ((a+b-m)/(n-m) * ((m+1)/(m+1-a))) ≤ 1 := by
    have hid : K * ((a+b-m)/(n-m) * ((m+1)/(m+1-a))) =
        (m-a)*(m+1)/(m*(m+1-a)) := by
      dsimp [K]
      field_simp
      rw [hmean]
      ring
    rw [hid]
    apply (div_le_one (mul_pos hm hma)).mpr
    nlinarith
  have htail : K * ((a+b-j)/(n-j) * ((j+1)/(j+1-a))) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hprod hK).trans hcentral
  have hratio : K * ((a+b-j)/(n-j) * ((j+1)/(j+1-a))) =
      (q * (a+b-j) / ((1-q)*(j+1-a))) /
        ((n-j)*m/((j+1)*(n-m))) := by
    dsimp [K]
    field_simp
  rw [hratio] at htail
  exact (div_le_one (by positivity : 0 < (n-j)*m/((j+1)*(n-m)))).mp htail

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma probability_pos_of_interior {p : ι → ℝ}
    (hp : ∀ i, 0 < p i ∧ p i < 1) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    0 < probability p k := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hk
  let b : ι → Bool := fun i => decide (i ∈ s)
  have hcount : count b = k := by simp [count, b, hcard]
  have hweight : 0 < weight p b := by
    apply Finset.prod_pos
    intro i hi
    split_ifs
    · exact (hp i).1
    · linarith [(hp i).2]
  unfold probability
  apply Finset.sum_pos'
  · intro c hc
    split_ifs
    · exact (weight_nonneg ⟨fun i => (hp i).1.le, fun i => (hp i).2.le⟩ c)
    · exact le_rfl
  · exact ⟨b, Finset.mem_univ b, by simpa [hcount] using hweight⟩

noncomputable def referenceProbability (m k : ℕ) : ℝ :=
  probability (fun _ : ι => (m : ℝ) / Fintype.card ι) k

lemma referenceProbability_pos (m k : ℕ) (hm : 0 < m) (hmn : m < Fintype.card ι)
    (hk : k ≤ Fintype.card ι) : 0 < referenceProbability (ι := ι) m k := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast lt_trans hm hmn
  apply probability_pos_of_interior _ k hk
  intro i
  constructor
  · exact div_pos (by exact_mod_cast hm) hn
  · exact (div_lt_one hn).mpr (by exact_mod_cast hmn)

omit [DecidableEq ι] in
lemma generating_constant (q : ℝ) :
    generating (fun _ : ι => q) = shiftedBinomial 0 (Fintype.card ι) q := by
  simp [generating, shiftedBinomial]

lemma referenceProbability_recurrence (m j : ℕ) (hn : 0 < Fintype.card ι) :
    ((j : ℝ)+1) * ((Fintype.card ι : ℝ)-m) * referenceProbability (ι := ι) m (j+1) =
      ((Fintype.card ι : ℝ)-j) * m * referenceProbability (ι := ι) m j := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have h := shiftedBinomial_coefficient_relation 0 (Fintype.card ι) j
    ((m : ℝ) / Fintype.card ι)
  rw [← generating_constant, generating_coeff, generating_coeff] at h
  simp only [Nat.cast_zero] at h
  change (((j : ℝ)+1)-0) * (1-(m : ℝ)/Fintype.card ι) *
      referenceProbability (ι := ι) m (j+1) =
    ((0+(Fintype.card ι : ℝ))-j) * ((m : ℝ)/Fintype.card ι) *
      referenceProbability (ι := ι) m j at h
  field_simp [hn'] at h
  nlinarith [h]

lemma profile_likelihood_step {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1)
    (a b m j : ℕ) (q : ℝ) (hq : 0 < q ∧ q < 1)
    (hab : a+b ≤ Fintype.card ι) (hmean : (m : ℝ) = a + b*q)
    (hpoly : generating p = shiftedBinomial a b q)
    (hm : 0 < m) (hmn : m < Fintype.card ι) (hmj : m ≤ j) (hjn : j < Fintype.card ι) :
    probability p (j+1) / referenceProbability (ι := ι) m (j+1) ≤
      probability p j / referenceProbability (ι := ι) m j := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < Fintype.card ι := by exact_mod_cast hmn
  have hmj' : (m : ℝ) ≤ j := by exact_mod_cast hmj
  have hjn' : (j : ℝ) < Fintype.card ι := by exact_mod_cast hjn
  have hab' : (a : ℝ) + b ≤ Fintype.card ι := by exact_mod_cast hab
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have ham : (a : ℝ) ≤ m := by rw [hmean]; nlinarith [mul_nonneg hb hq.1.le]
  have hja : 0 < (j : ℝ)+1-a := by linarith
  have hq1 : 0 < 1-q := by linarith
  have hnj : 0 < (Fintype.card ι : ℝ)-j := by linarith
  have hnm : 0 < (Fintype.card ι : ℝ)-m := by linarith
  have hj1 : 0 < (j : ℝ)+1 := by linarith
  let rP := q * ((a : ℝ)+b-j) / ((1-q)*((j : ℝ)+1-a))
  let rB := ((Fintype.card ι : ℝ)-j)*m/(((j : ℝ)+1)*((Fintype.card ι : ℝ)-m))
  have hr : rP ≤ rB := profile_tail_ratio_le ha hb hab' hm' hmn' hmj' hjn' hq hmean
  have hP : probability p (j+1) = rP * probability p j := by
    have h := shiftedBinomial_coefficient_relation a b j q
    rw [← hpoly, generating_coeff, generating_coeff] at h
    dsimp [rP]
    field_simp
    nlinarith [h]
  have hB : referenceProbability (ι := ι) m (j+1) = rB * referenceProbability (ι := ι) m j := by
    have h := referenceProbability_recurrence (ι := ι) m j (lt_trans hm hmn)
    dsimp [rB]
    field_simp
    nlinarith [h]
  have hcross : probability p (j+1) * referenceProbability (ι := ι) m j ≤
      probability p j * referenceProbability (ι := ι) m (j+1) := by
    rw [hP, hB]
    have h := mul_le_mul_of_nonneg_right hr
      (mul_nonneg (probability_nonneg hp j)
        (referenceProbability_pos m j hm hmn hjn.le).le)
    nlinarith [h]
  exact (div_le_div_iff₀ (referenceProbability_pos m (j+1) hm hmn (by omega))
    (referenceProbability_pos m j hm hmn hjn.le)).mpr hcross

lemma profile_likelihood_upper_tail {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1)
    (a b m k : ℕ) (q : ℝ) (hq : 0 < q ∧ q < 1)
    (hab : a+b ≤ Fintype.card ι) (hmean : (m : ℝ) = a + b*q)
    (hpoly : generating p = shiftedBinomial a b q)
    (hm : 0 < m) (hmn : m < Fintype.card ι) (hmk : m ≤ k) (hkn : k ≤ Fintype.card ι) :
    probability p k / referenceProbability (ι := ι) m k ≤
      probability p m / referenceProbability (ι := ι) m m := by
  revert hkn
  induction k, hmk using Nat.le_induction with
  | base => intro h; exact le_rfl
  | succ k hmk ih =>
    intro hkn
    exact (profile_likelihood_step hp a b m k q hq hab hmean hpoly hm hmn hmk (by omega)).trans
      (ih (by omega))

theorem probability_likelihood_upper_tail (p : ι → ℝ) (m k : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 0 < m) (hmn : m < Fintype.card ι)
    (hmk : m ≤ k) (hkn : k ≤ Fintype.card ι) :
    probability p k / referenceProbability (ι := ι) m k ≤
      probability p m / referenceProbability (ι := ι) m m := by
  let f : ℕ → ℝ := fun j => (1 / referenceProbability (ι := ι) m k) *
    (if j = k then 1 else 0) - (1 / referenceProbability (ι := ι) m m) *
      (if j = m then 1 else 0)
  have hF (v : ι → ℝ) : expectation f v =
      probability v k / referenceProbability (ι := ι) m k -
        probability v m / referenceProbability (ι := ι) m m := by
    dsimp only [f]
    rw [expectation_probability_difference]
    ring
  obtain ⟨v, a, b, q, hv, hmax, hq, hab, hmean, hpoly⟩ :=
    exists_fixed_mean_binomial_maximizer f (m : ℝ) ⟨p, hp⟩
  have hvbound := profile_likelihood_upper_tail hv.1 a b m k q hq hab hmean hpoly hm hmn hmk hkn
  have h := hmax p hp
  rw [hF, hF] at h
  linarith

lemma referenceProbability_complement (m k : ℕ) (hn : 0 < Fintype.card ι)
    (hmn : m ≤ Fintype.card ι) (hkn : k ≤ Fintype.card ι) :
    referenceProbability (ι := ι) (Fintype.card ι - m) (Fintype.card ι - k) =
      referenceProbability (ι := ι) m k := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold referenceProbability
  rw [← probability_complement (fun _ : ι => (m : ℝ)/Fintype.card ι) k hkn]
  congr 1
  funext i
  rw [Nat.cast_sub hmn]
  field_simp

/-- The binomial likelihood ratio is largest at the integer mean. -/
theorem probability_central_likelihood (p : ι → ℝ) (m k : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 0 < m) (hmn : m < Fintype.card ι)
    (hkn : k ≤ Fintype.card ι) :
    probability p k / referenceProbability (ι := ι) m k ≤
      probability p m / referenceProbability (ι := ι) m m := by
  by_cases hmk : m ≤ k
  · exact probability_likelihood_upper_tail p m k hp hm hmn hmk hkn
  · have hn := lt_trans hm hmn
    have h := probability_likelihood_upper_tail (fun i => 1-p i)
      (Fintype.card ι-m) (Fintype.card ι-k) (complement_mem_parameters hp)
      (by omega) (by omega) (by omega) (by omega)
    rw [probability_complement p k hkn, probability_complement p m hmn.le,
      referenceProbability_complement m k hn hmn.le hkn,
      referenceProbability_complement m m hn hmn.le hmn.le] at h
    exact h

lemma sum_referenceProbability (m : ℕ) :
    (∑ k ∈ Finset.range (Fintype.card ι+1), referenceProbability (ι := ι) m k) = 1 :=
  sum_probability (fun _ : ι => (m : ℝ)/Fintype.card ι)

/-- The central likelihood ratio is at least one. -/
theorem one_le_central_likelihood (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 0 < m) (hmn : m < Fintype.card ι) :
    1 ≤ probability p m / referenceProbability (ι := ι) m m := by
  have hsum : (∑ k ∈ Finset.range (Fintype.card ι+1), probability p k) ≤
      (∑ k ∈ Finset.range (Fintype.card ι+1), referenceProbability (ι := ι) m k) *
        (probability p m / referenceProbability (ι := ι) m m) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k ≤ Fintype.card ι := by simpa using Finset.mem_range.mp hk
    have h := (div_le_iff₀ (referenceProbability_pos m k hm hmn hkn)).mp
      (probability_central_likelihood p m k hp hm hmn hkn)
    simpa only [mul_comm] using h
  simpa only [sum_probability, sum_referenceProbability, one_mul] using hsum

/-- The squared likelihood norm is bounded by the central likelihood ratio. -/
theorem likelihood_norm_le_central (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 0 < m) (hmn : m < Fintype.card ι) :
    (∑ k ∈ Finset.range (Fintype.card ι+1),
      probability p k ^ 2 / referenceProbability (ι := ι) m k) ≤
        probability p m / referenceProbability (ι := ι) m m := by
  calc
    (∑ k ∈ Finset.range (Fintype.card ι+1),
      probability p k ^ 2 / referenceProbability (ι := ι) m k) ≤
        ∑ k ∈ Finset.range (Fintype.card ι+1), probability p k *
          (probability p m / referenceProbability (ι := ι) m m) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ Fintype.card ι := by simpa using Finset.mem_range.mp hk
      calc
        probability p k ^ 2 / referenceProbability (ι := ι) m k =
            probability p k * (probability p k / referenceProbability (ι := ι) m k) := by ring
        _ ≤ probability p k * (probability p m / referenceProbability (ι := ι) m m) :=
          mul_le_mul_of_nonneg_left (probability_central_likelihood p m k hp hm hmn hkn)
            (probability_nonneg hp.1 k)
    _ = probability p m / referenceProbability (ι := ι) m m := by
      rw [← Finset.sum_mul, sum_probability, one_mul]

lemma generating_second_derivative_eval_one (p : ι → ℝ) :
    (derivative (derivative (generating p))).eval 1 = (∑ i, p i)^2 - ∑ i, p i^2 := by
  have hexp : (derivative (derivative (generating p))).eval 1 =
      ∑ i, (∑ j ∈ Finset.univ.erase i, p j) * p i := by
    unfold generating
    rw [derivative_prod_finset, derivative_sum, eval_finsetSum]
    simp [derivative_mul, derivative_prod_finset, eval_finsetSum, eval_prod]
  have hsum (i : ι) : (∑ j ∈ Finset.univ.erase i, p j) = (∑ j, p j) - p i := by
    have h := Finset.add_sum_erase Finset.univ p (Finset.mem_univ i)
    linarith
  rw [hexp]
  simp_rw [hsum, sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [pow_two]

lemma probability_eq_zero_of_card_lt (p : ι → ℝ) (k : ℕ) (hk : Fintype.card ι < k) :
    probability p k = 0 := by
  unfold probability
  apply Finset.sum_eq_zero
  intro b hb
  have hne : count b ≠ k := by have h := count_le_card b; omega
  simp only [hne, ite_false]

lemma probability_eq_reference_of_central_eq_one (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 0 < m) (hmn : m < Fintype.card ι)
    (heq : probability p m / referenceProbability (ι := ι) m m = 1) :
    ∀ k, probability p k = referenceProbability (ι := ι) m k := by
  have hle (k : ℕ) (hk : k ≤ Fintype.card ι) :
      probability p k ≤ referenceProbability (ι := ι) m k := by
    have h := probability_central_likelihood p m k hp hm hmn hk
    rw [heq] at h
    exact (div_le_one (referenceProbability_pos m k hm hmn hk)).mp h
  have hsum : (∑ k ∈ Finset.range (Fintype.card ι+1),
      (referenceProbability (ι := ι) m k - probability p k)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_referenceProbability, sum_probability, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk =>
    sub_nonneg.mpr (hle k (by simpa using Finset.mem_range.mp hk)))).mp hsum
  intro k
  by_cases hk : k ≤ Fintype.card ι
  · have h := hzero k (Finset.mem_range.mpr (by omega))
    linarith
  · have hgt : Fintype.card ι < k := by omega
    rw [probability_eq_zero_of_card_lt p k hgt]
    exact (probability_eq_zero_of_card_lt (fun _ : ι => (m : ℝ)/Fintype.card ι) k hgt).symm

lemma generating_eq_constant_of_central_eq_one (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 0 < m) (hmn : m < Fintype.card ι)
    (heq : probability p m / referenceProbability (ι := ι) m m = 1) :
    generating p = generating (fun _ : ι => (m : ℝ)/Fintype.card ι) := by
  ext k
  rw [generating_coeff, generating_coeff]
  exact probability_eq_reference_of_central_eq_one p m hp hm hmn heq k

lemma parameters_eq_of_generating_eq_constant (p : ι → ℝ) (q : ℝ)
    (hmean : (∑ i, p i) = Fintype.card ι * q)
    (heq : generating p = generating (fun _ : ι => q)) : ∀ i, p i = q := by
  have hd := congrArg (fun P : Polynomial ℝ => (derivative (derivative P)).eval 1) heq
  rw [generating_second_derivative_eval_one, generating_second_derivative_eval_one] at hd
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hd
  have hsq : (∑ i, (p i-q)^2) = 0 := by
    have hterm (i : ι) : (p i-q)^2 = p i^2 - 2*q*p i + q^2 := by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hmean] at hd ⊢
    nlinarith [hd]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sq_nonneg (p i-q))).mp hsq
  intro i
  have h := hz i (Finset.mem_univ i)
  nlinarith [sq_nonneg (p i-q)]

/-- Equality in the central lower bound forces equal Bernoulli parameters. -/
theorem central_likelihood_eq_one_iff (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hm : 0 < m) (hmn : m < Fintype.card ι) :
    probability p m / referenceProbability (ι := ι) m m = 1 ↔
      ∀ i, p i = (m : ℝ)/Fintype.card ι := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_trans hm hmn)
  constructor
  · intro heq
    apply parameters_eq_of_generating_eq_constant p ((m : ℝ)/Fintype.card ι)
    · have hsum : (∑ i, p i) = (m : ℝ) := hp.2
      rw [hsum]
      field_simp
    · exact generating_eq_constant_of_central_eq_one p m hp hm hmn heq
  · intro heq
    have hpconst : p = fun _ : ι => (m : ℝ)/Fintype.card ι := funext heq
    rw [hpconst]
    exact div_self (ne_of_gt (referenceProbability_pos m m hm hmn hmn.le))

lemma probability_deterministic (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hdet : ∀ i, p i = 0 ∨ p i = 1) (k : ℕ) :
    probability p k = if k = m then 1 else 0 := by
  classical
  have hnone (i : ι) : ¬(0 < p i ∧ p i < 1) := by
    rcases hdet i with h | h <;> simp [h]
  have hconst : ∀ i, (0 < p i ∧ p i < 1) → p i = (0 : ℝ) := by
    intro i hi
    exact False.elim (hnone i hi)
  have hfrac : fractional p = ∅ := by
    ext i
    simp [fractional, hnone i]
  have hsum := sum_of_equal_interior hp.1 0 hconst
  have hmean : (∑ i, p i) = (m : ℝ) := hp.2
  rw [hmean, hfrac] at hsum
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul, add_zero] at hsum
  have ha : (ones p).card = m := by exact_mod_cast hsum.symm
  have hgen := generating_of_equal_interior hp.1 0 hconst
  rw [hfrac, ha] at hgen
  simp only [Finset.card_empty, pow_zero, mul_one] at hgen
  rw [← generating_coeff, hgen, coeff_X_pow]

/-- Deterministic laws also attain the squared likelihood norm bound. -/
theorem likelihood_norm_eq_of_deterministic (p : ι → ℝ) (m : ℕ)
    (hp : p ∈ parameters (m : ℝ)) (hdet : ∀ i, p i = 0 ∨ p i = 1) :
    (∑ k ∈ Finset.range (Fintype.card ι+1),
      probability p k ^ 2 / referenceProbability (ι := ι) m k) =
        probability p m / referenceProbability (ι := ι) m m := by
  simp_rw [probability_deterministic p m hp hdet]
  simp [ite_pow, ite_div, Nat.lt_succ_of_le (mean_le_card hp)]


end MathAndTheory.Gyires.Bernoulli
