import HahnBoundary
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Residue representatives in algebraic valued extensions

This file proves the residue-lifting step used at the valuation-zero boundary
of the forward implication. It uses algebraicity, algebraic closedness of the
constant field, and actual residue representatives in the base. Henselianity
is not needed for this step.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace NTCThird

set_option maxHeartbeats 1200000

theorem addValuation_div_nonneg_of_le
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℚ))
    {a b : K} (hb : b ≠ 0) (hab : v b ≤ v a) : 0 ≤ v (a / b) := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr ha)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hb)
  rw [v.map_div, ← hr, ← hs]
  rw [← hr, ← hs] at hab
  have hsr : s ≤ r := WithTop.coe_le_coe.mp hab
  simpa only [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_zero,
    WithTop.coe_le_coe] using
    (sub_nonneg.mpr hsr : 0 ≤ r - s)

theorem addValuation_multiset_prod_value
    {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℚ)) (s : Multiset R) :
    v s.prod = (s.map v).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih]

/-- If no constant has positive-distance residue agreement, evaluation of
every nonzero polynomial over the algebraically closed constants has value zero. -/
theorem eval₂_value_zero_of_constant_distances
    {k E : Type*} [Field k] [IsAlgClosed k] [Field E]
    (f : k →+* E) (v : AddValuation E (WithTop ℚ))
    (hconst : ∀ c : k, c ≠ 0 → v (f c) = 0)
    (u : E) (hdist : ∀ c : k, v (u - f c) = 0)
    (Q : k[X]) (hQ : Q ≠ 0) : v (Q.eval₂ f u) = 0 := by
  rw [(IsAlgClosed.splits Q).eq_prod_roots]
  rw [eval₂_mul, eval₂_C, v.map_mul,
    hconst Q.leadingCoeff (leadingCoeff_ne_zero.mpr hQ), zero_add,
    eval₂_multiset_prod, addValuation_multiset_prod_value,
    Multiset.map_map, Multiset.map_map]
  simp [Function.comp_def, hdist]

/-- Algebraic extension does not enlarge an algebraically closed residue
field. The hypotheses and conclusion are stated using the actual valuations,
so this applies in particular to every approximant in an algebraic closure. -/
theorem algebraic_residue_lift
    {k K E : Type*} [Field k] [IsAlgClosed k] [Field K] [Field E] [Algebra K E]
    (C : k →+* K) (vK : AddValuation K (WithTop ℚ))
    (v : AddValuation E (WithTop ℚ))
    (hext : ∀ a : K, v (algebraMap K E a) = vK a)
    (hconst : ∀ c : k, c ≠ 0 → vK (C c) = 0)
    (hres : ∀ a : K, 0 ≤ vK a → ∃ c : k, 0 < vK (a - C c))
    (u : E) (hu : IsIntegral K u) (hvu : 0 ≤ v u) :
    ∃ c : k, 0 < v (u - algebraMap K E (C c)) := by
  classical
  let f : k →+* E := (algebraMap K E).comp C
  have hconstE : ∀ c : k, c ≠ 0 → v (f c) = 0 := by
    intro c hc
    exact (hext (C c)).trans (hconst c hc)
  by_contra hno
  have hdist : ∀ c : k, v (u - f c) = 0 := by
    intro c
    apply le_antisymm
    · exact le_of_not_gt (fun h => hno ⟨c, h⟩)
    · apply v.map_le_sub hvu
      by_cases hc : c = 0
      · simp [hc]
      · exact (hconstE c hc).ge
  let P : K[X] := minpoly K u
  have hP : P ≠ 0 := minpoly.ne_zero hu
  obtain ⟨j, hj, hmin⟩ := P.support.exists_min_image
    (fun i => vK (P.coeff i)) ((Polynomial.support_nonempty).mpr hP)
  have haj : P.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  let b : ℕ → K := fun i => P.coeff i / P.coeff j
  have hb : ∀ i, 0 ≤ vK (b i) := by
    intro i
    apply addValuation_div_nonneg_of_le vK haj
    by_cases hi : i ∈ P.support
    · exact hmin i hi
    · simp only [Polynomial.mem_support_iff, not_not] at hi
      simp [hi]
  choose c hc using fun i => hres (b i) (hb i)
  have hbj : b j = 1 := div_self haj
  have hcj : c j = 1 := by
    by_contra h
    have hn : 1 - c j ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hz : vK (b j - C (c j)) = 0 := by
      rw [hbj, ← map_one C, ← map_sub, hconst _ hn]
    exact (ne_of_gt (hc j)) hz
  let Q : k[X] := ∑ i ∈ P.support, Polynomial.monomial i (c i)
  have hQj : Q.coeff j = 1 := by
    simp [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hj, hcj]
  have hQ : Q ≠ 0 := by
    intro h
    have := hQj
    simp [h] at this
  have hQvalue : v (Q.eval₂ f u) = 0 :=
    eval₂_value_zero_of_constant_distances f v hconstE u hdist Q hQ
  have hPsum : ∑ i ∈ P.support, algebraMap K E (P.coeff i) * u ^ i = 0 := by
    have hm := minpoly.aeval K u
    simpa only [aeval_def, eval₂_eq_sum, Polynomial.sum_def] using hm
  have hbsum : ∑ i ∈ P.support, algebraMap K E (b i) * u ^ i = 0 := by
    simp_rw [b, div_eq_mul_inv, map_mul]
    calc
      ∑ i ∈ P.support,
          (algebraMap K E (P.coeff i) * algebraMap K E (P.coeff j)⁻¹) * u ^ i =
          (∑ i ∈ P.support, algebraMap K E (P.coeff i) * u ^ i) *
            algebraMap K E (P.coeff j)⁻¹ := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = 0 := by rw [hPsum, zero_mul]
  have herr : 0 < v (∑ i ∈ P.support,
      algebraMap K E (b i - C (c i)) * u ^ i) := by
    apply v.map_lt_sum (by simp)
    intro i hi
    rw [v.map_mul, hext]
    exact lt_of_lt_of_le (hc i) (le_add_of_nonneg_right (by
      rw [v.map_pow]
      exact nsmul_nonneg hvu i))
  have heq : (∑ i ∈ P.support,
      algebraMap K E (b i - C (c i)) * u ^ i) = -(Q.eval₂ f u) := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, hbsum, zero_sub]
    congr 1
    simp [Q, f, Polynomial.eval₂_finset_sum]
  rw [heq, v.map_neg, hQvalue] at herr
  exact (lt_irrefl _ herr)

section Hahn

attribute [local instance 2000] HahnSeries.instAlgebra

/-- Taking the coefficient of exponent zero supplies the actual residue
representative of every nonnegative Hahn series. -/
theorem hahn_residue_coefficient_lift
    {k : Type*} [Field k] (a : HahnSeries ℚ k)
    (ha : 0 ≤ HahnSeries.addVal ℚ k a) :
    0 < HahnSeries.addVal ℚ k
      (a - algebraMap k (HahnSeries ℚ k) (a.coeff 0)) := by
  apply lt_orderTop_of_coeff_zero_le
  intro q hq
  rcases lt_or_eq_of_le hq with hlt | rfl
  · have hz : a.coeff q = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) ha)
    simp [HahnSeries.coeff_sub, hz, HahnSeries.algebraMap_apply,
      HahnSeries.coeff_single, ne_of_lt hlt]
  · simp [HahnSeries.coeff_sub, HahnSeries.algebraMap_apply]

/-- Residue lifting for every algebraic extension of an actual Hahn subfield.
The chosen representative is an actual element of that base field. -/
theorem algebraic_hahn_residue_lift
    {k E : Type*} [Field k] [IsAlgClosed k] [Field E]
    (K : IntermediateField k (HahnSeries ℚ k)) [Algebra K E]
    (v : AddValuation E (WithTop ℚ))
    (hext : ∀ a : K, v (algebraMap K E a) = HahnSeries.addVal ℚ k a)
    (u : E) (hu : IsIntegral K u) (hvu : 0 ≤ v u) :
    ∃ a : K, 0 < v (u - algebraMap K E a) := by
  let vK : AddValuation K (WithTop ℚ) :=
    (HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)
  have hconst : ∀ c : k, c ≠ 0 → vK (algebraMap k K c) = 0 := by
    intro c hc
    exact hahn_nonzero_constant_value c hc
  have hres : ∀ a : K, 0 ≤ vK a →
      ∃ c : k, 0 < vK (a - algebraMap k K c) := by
    intro a ha
    refine ⟨(a : HahnSeries ℚ k).coeff 0, ?_⟩
    exact hahn_residue_coefficient_lift (k := k) (a : HahnSeries ℚ k) ha
  obtain ⟨c, hc⟩ := algebraic_residue_lift (k := k) (K := K) (E := E)
    (algebraMap k K) vK v hext
    hconst hres u hu hvu
  exact ⟨algebraMap k K c, hc⟩

end Hahn

end NTCThird
