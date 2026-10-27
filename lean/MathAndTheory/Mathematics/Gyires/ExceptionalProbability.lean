module

public import MathAndTheory.Mathematics.Gyires.OneSuccess
public import MathAndTheory.Mathematics.Gyires.ExceptionalScalar

@[expose] public section

open scoped BigOperators
open Finset

namespace MathAndTheory.Gyires.Exceptional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalar_probability_bounds (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1)
    (hsum : ∑ i, u i = 1) (k : ℕ) (hcard : Fintype.card ι = k+2) :
    scalarR k (secondMoment u) ≤ (oneSuccess u)^2 ∧
      (1/((k : ℝ)+2) < secondMoment u → scalarR k (secondMoment u) < (oneSuccess u)^2) := by
  have hb := secondMoment_bounds u hu hsum (by omega : 0 < Fintype.card ι)
  rw [hcard] at hb
  push_cast at hb
  have hbase : (0 : ℝ) < 1/((k : ℝ)+2) := by positivity
  have ha0 : 0 < secondMoment u := hbase.trans_le hb.1
  have hQ := secondMoment_le_oneSuccess u hu hsum
  have hQ0 : 0 < oneSuccess u := ha0.trans_le hQ
  by_cases hh : secondMoment u ≤ 1/2
  · have hint (i : ι) : u i < 1 := by
      have hi : u i^2 ≤ secondMoment u :=
        Finset.single_le_sum (fun j hj => sq_nonneg (u j)) (Finset.mem_univ i)
      have hui : u i ≤ 1 := hu.2 i
      nlinarith
    have hl := log_oneSuccess_refined u hu hsum hint k hcard
    have hs := scalarLog_small_bounds k (secondMoment u) hb.1 hh
    rw [scalarLog_base] at hs
    have hexp : Real.exp (scalarLog k (secondMoment u)) = scalarR k (secondMoment u) := by
      rw [scalarLog_eq_log k _ ha0, Real.exp_log (scalarR_pos k _ ha0)]
    constructor
    · have he := Real.exp_le_exp.mpr (hs.1.trans hl)
      simpa only [hexp, exp_two_log hQ0] using he
    · intro hgt
      have he := Real.exp_lt_exp.mpr ((hs.2 hgt).trans_le hl)
      simpa only [hexp, exp_two_log hQ0] using he
  · have hh' : 1/2 < secondMoment u := lt_of_not_ge hh
    have hr := scalarR_large_bounds k (secondMoment u) ⟨hh'.le, hb.2⟩
    have hsq : (secondMoment u)^2 ≤ (oneSuccess u)^2 := by nlinarith
    exact ⟨hr.1.trans hsq, fun _ => (hr.2 hh').trans_le hsq⟩

omit [DecidableEq ι] in
lemma parameters_constant_of_secondMoment (u : ι → ℝ) (hsum : ∑ i, u i = 1)
    (k : ℕ) (hcard : Fintype.card ι = k+2)
    (ha : secondMoment u = 1/((k : ℝ)+2)) : ∀ i, u i = 1/((k : ℝ)+2) := by
  have hn : (0 : ℝ) < (k : ℝ)+2 := by positivity
  have hs : (∑ i, (u i - 1/((k : ℝ)+2))^2) = 0 := by
    have ht (i : ι) : (u i - 1/((k : ℝ)+2))^2 =
        u i^2 - (2/((k : ℝ)+2))*u i + (1/((k : ℝ)+2))^2 := by ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hsum, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    change secondMoment u - (2/((k : ℝ)+2))*1 + ((k+2 : ℕ) : ℝ)*(1/((k : ℝ)+2))^2 = 0
    rw [ha]
    push_cast
    field_simp
    ring
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg _)).mp hs i (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)

theorem scalar_probability_eq_implies_constant (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1)
    (hsum : ∑ i, u i = 1) (k : ℕ) (hcard : Fintype.card ι = k+2)
    (heq : scalarR k (secondMoment u) = (oneSuccess u)^2) :
    ∀ i, u i = 1/((k : ℝ)+2) := by
  apply parameters_constant_of_secondMoment u hsum k hcard
  have hb := (secondMoment_bounds u hu hsum (by omega : 0 < Fintype.card ι)).1
  rw [hcard] at hb
  push_cast at hb
  apply le_antisymm _ hb
  by_contra h
  have hs := (scalar_probability_bounds u hu hsum k hcard).2 (lt_of_not_ge h)
  linarith


end MathAndTheory.Gyires.Exceptional
