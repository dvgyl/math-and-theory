module

public import SubsetOrbit
public import MathAndTheory.Mathematics.Gyires.BernoulliMaximizer
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

open scoped BigOperators
open Polynomial Finset

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def elementaryGenerating (u : ι → ℝ) : ℝ[X] :=
  ∏ i, (1 + C (u i) * X)

omit [DecidableEq ι] in
lemma elementaryGenerating_eq_sum (u : ι → ℝ) :
    elementaryGenerating u =
      ∑ k ∈ range (Fintype.card ι + 1), C (elementary u k) * X ^ k := by
  unfold elementaryGenerating
  rw [Finset.prod_one_add]
  have hterm (S : Finset ι) : (∏ i ∈ S, C (u i) * X) = C (∏ i ∈ S, u i) * X ^ S.card := by
    rw [Finset.prod_mul_distrib, ← map_prod]
    simp
  simp_rw [hterm]
  rw [Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro k _
  have hcard : ∀ S ∈ (univ : Finset ι).powersetCard k,
      C (∏ i ∈ S, u i) * X ^ S.card = C (∏ i ∈ S, u i) * X ^ k := by
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hcard, ← Finset.sum_mul, ← map_sum]
  rfl

omit [DecidableEq ι] in
lemma elementaryGenerating_coeff (u : ι → ℝ) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    (elementaryGenerating u).coeff k = elementary u k := by
  rw [elementaryGenerating_eq_sum]
  simp [Polynomial.finsetSum_coeff, hk]

lemma sum_weight_count_polynomial (p : ι → ℝ) (f : ℕ → ℝ[X]) :
    (∑ b : ι → Bool, C (weight p b) * f (count b)) =
      ∑ k ∈ range (Fintype.card ι + 1), C (probability p k) * f k := by
  unfold probability
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [apply_ite, Finset.sum_ite_eq, Nat.lt_succ_of_le (count_le_card b)]

/-- This polynomial identity has no exceptional value of the polynomial variable. -/
theorem centered_generating_eq_law (p : ι → ℝ) (θ : ℝ) :
    elementaryGenerating (fun i => p i - θ) =
      ∑ k ∈ range (Fintype.card ι + 1), C (probability p k) *
        ((1 - C θ * X) ^ (Fintype.card ι-k) * (1 + C (1-θ) * X) ^ k) := by
  let P : ℝ[X] := 1 - C θ * X
  let R : ℝ[X] := 1 + C (1-θ) * X
  let g (i : ι) (b : Bool) : ℝ[X] := if b then C (p i) * R else C (1-p i) * P
  have hsum (i : ι) : 1 + C (p i - θ) * X = ∑ b : Bool, g i b := by
    simp [g, P, R, map_sub]
    ring
  unfold elementaryGenerating
  simp_rw [hsum]
  rw [Fintype.prod_sum]
  have hterm (b : ι → Bool) : (∏ i, g i (b i)) =
      C (weight p b) * (P ^ (Fintype.card ι-count b) * R ^ count b) := by
    have heq (i : ι) : g i (b i) =
        C (if b i then p i else 1-p i) *
          P ^ (if b i then 0 else 1 : ℕ) * R ^ (if b i then 1 else 0 : ℕ) := by
      cases b i <;> simp [g]
    have hfalse : (∑ i, if b i then 0 else 1 : ℕ) = Fintype.card ι-count b := by
      have hb (i : ι) : (if b i then 0 else 1 : ℕ) = if !(b i) then 1 else 0 := by
        cases b i <;> rfl
      simp_rw [hb]
      change count (fun i => !(b i)) = Fintype.card ι-count b
      have h := count_complement b
      omega
    simp_rw [heq]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hfalse]
    change C (weight p b) * P ^ (Fintype.card ι-count b) * R ^ count b = _
    ring
  simp_rw [hterm]
  exact sum_weight_count_polynomial p (fun k => P ^ (Fintype.card ι-k) * R ^ k)

/-- Each centered elementary symmetric polynomial is a linear function of the law. -/
theorem centered_elementary_eq_law (p : ι → ℝ) (θ : ℝ) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    elementary (fun i => p i - θ) k =
      ∑ j ∈ range (Fintype.card ι + 1), probability p j *
        (((1 - C θ * X) ^ (Fintype.card ι-j) * (1 + C (1-θ) * X) ^ j : ℝ[X]).coeff k) := by
  rw [← elementaryGenerating_coeff _ k hk, centered_generating_eq_law]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

end MathAndTheory.Gyires.RankTwo
