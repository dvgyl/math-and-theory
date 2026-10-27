module

public import LawTransform
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

@[expose] public section

open scoped BigOperators
open Finset Polynomial

namespace MathAndTheory.Gyires.RankTwo

lemma multiset_elementary_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

lemma multiset_elementary_two_cons (a : ℝ) (s : Multiset ℝ) :
    (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
  change ((Multiset.powersetCard (1+1) (a ::ₘ s)).map Multiset.prod).sum = _
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  simp only [Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]
  change s.esymm 2 + a * s.esymm 1 = _
  rw [multiset_elementary_one]

lemma multiset_second_identity (s : Multiset ℝ) :
    s.sum ^ 2 = (s.map (fun x => x ^ 2)).sum + 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | @cons a s ih =>
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
        multiset_elementary_two_cons]
      nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem elementary_two_identity (u : ι → ℝ) :
    (∑ i, u i) ^ 2 = (∑ i, (u i) ^ 2) + 2 * elementary u 2 := by
  have h := multiset_second_identity ((univ : Finset ι).val.map u)
  simp only [Multiset.map_map, Function.comp_apply, Finset.esymm_map_val,
    ← Finset.sum_eq_multiset_sum] at h
  exact h

omit [DecidableEq ι] in
theorem variance_eq_neg_two_elementary (u : ι → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, (u i) ^ 2) = -2 * elementary u 2 := by
  have h := elementary_two_identity u
  rw [hu] at h
  nlinarith

theorem centered_variance_eq_law (p : ι → ℝ) (θ : ℝ)
    (hn : 2 ≤ Fintype.card ι) (hp : ∑ i, (p i - θ) = 0) :
    (∑ i, (p i - θ) ^ 2) =
      ∑ j ∈ range (Fintype.card ι + 1), Bernoulli.probability p j *
        (-2 * (((1 - C θ * X) ^ (Fintype.card ι-j) *
          (1 + C (1-θ) * X) ^ j : ℝ[X]).coeff 2)) := by
  rw [variance_eq_neg_two_elementary _ hp, centered_elementary_eq_law p θ 2 hn,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end MathAndTheory.Gyires.RankTwo
