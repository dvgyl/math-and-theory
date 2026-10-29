module
public import ProductCoefficients
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
Conversion of a positive-spectrum factorization into characteristic
coefficients. This is a polynomial theorem. The matrix factorization itself
is not assumed as a definition and must be supplied by the matrix proof.
-/

namespace UnicyclicProduct

open scoped BigOperators
open Polynomial

variable {ι : Type*}

noncomputable def shiftedProduct (s : Finset ι) (theta : ι → ℝ) : Polynomial ℝ :=
  ∏ i ∈ s, (X+C (theta i))

theorem shiftedProduct_factorization (s : Finset ι) (theta : ι → ℝ)
    (htheta : ∀ i ∈ s, theta i ≠ 0) :
    shiftedProduct s theta =
      C (∏ i ∈ s, theta i) * linearProduct s (fun i => 1/theta i) := by
  have hpoint : ∀ i ∈ s,
      X+C (theta i) = C (theta i)*(1+C (1/theta i)*X) := by
    intro i hi
    have hprod : C (theta i)*C (1/theta i) = (1 : Polynomial ℝ) := by
      rw [← map_mul]
      simp [one_div, htheta i hi]
    rw [mul_add, mul_one, ← mul_assoc, hprod, one_mul]
    ring
  dsimp [shiftedProduct, linearProduct]
  calc
    (∏ i ∈ s, (X+C (theta i))) =
        ∏ i ∈ s, C (theta i)*(1+C (1/theta i)*X) := Finset.prod_congr rfl hpoint
    _ = (∏ i ∈ s, C (theta i)) * (∏ i ∈ s, (1+C (1/theta i)*X)) :=
      Finset.prod_mul_distrib
    _ = C (∏ i ∈ s, theta i) * (∏ i ∈ s, (1+C (1/theta i)*X)) := by
      rw [map_prod]

theorem characteristic_coefficients_from_spectrum
    (s : Finset ι) (theta : ι → ℝ) (P : Polynomial ℝ) (d : ℝ)
    (htheta : ∀ i ∈ s, theta i ≠ 0)
    (hd : d = ∏ i ∈ s, theta i)
    (hfactor : P+C d = shiftedProduct s theta) :
    P.coeff 1 = d*(∑ i ∈ s, 1/theta i) ∧
    P.coeff 2 = d*((∑ i ∈ s, 1/theta i)^2 - ∑ i ∈ s, (1/theta i)^2)/2 ∧
    P.coeff 3 = d*((∑ i ∈ s, 1/theta i)^3 -
      3*(∑ i ∈ s, 1/theta i)*(∑ i ∈ s, (1/theta i)^2) +
      2*(∑ i ∈ s, (1/theta i)^3))/6 := by
  have hid : P+C d = C d * linearProduct s (fun i => 1/theta i) := by
    rw [hfactor, shiftedProduct_factorization s theta htheta, ← hd]
  have hc1 := congrArg (fun Q : Polynomial ℝ => Q.coeff 1) hid
  have hc2 := congrArg (fun Q : Polynomial ℝ => Q.coeff 2) hid
  have hc3 := congrArg (fun Q : Polynomial ℝ => Q.coeff 3) hid
  norm_num [coeff_add, coeff_C, coeff_C_mul] at hc1 hc2 hc3
  obtain ⟨_,h1,h2,h3⟩ := linearProduct_coefficients s (fun i => 1/theta i)
  simp only [one_div] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [h1] at hc1
    exact hc1
  · have hm := congrArg (fun r : ℝ => d*r) h2
    rw [hc2]
    nlinarith only [hm]
  · have hm := congrArg (fun r : ℝ => d*r) h3
    rw [hc3]
    nlinarith only [hm]

theorem normalized_characteristic_coefficients_from_spectrum
    (s : Finset ι) (theta : ι → ℝ) (P : Polynomial ℝ) (d T : ℝ)
    (htheta : ∀ i ∈ s, theta i ≠ 0)
    (hd : d = ∏ i ∈ s, theta i)
    (hfactor : P+C d = shiftedProduct s theta)
    (hT : T = ∑ i ∈ s, 1/theta i) (hTnz : T ≠ 0) :
    P.coeff 1 = d*T ∧
    P.coeff 2 = d*T^2*(1-∑ i ∈ s, ((1/theta i)/T)^2)/2 ∧
    P.coeff 3 = d*T^3*(1-3*(∑ i ∈ s, ((1/theta i)/T)^2) +
      2*(∑ i ∈ s, ((1/theta i)/T)^3))/6 := by
  obtain ⟨h1,h2,h3⟩ := characteristic_coefficients_from_spectrum
    s theta P d htheta hd hfactor
  have hm2 : (∑ i ∈ s, ((1/theta i)/T)^2) =
      (∑ i ∈ s, (1/theta i)^2)/T^2 := by
    simp_rw [div_pow]
    rw [Finset.sum_div]
  have hm3 : (∑ i ∈ s, ((1/theta i)/T)^3) =
      (∑ i ∈ s, (1/theta i)^3)/T^3 := by
    simp_rw [div_pow]
    rw [Finset.sum_div]
  rw [← hT] at h1 h2 h3
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, hm2]
    field_simp <;> ring
  · rw [h3, hm2, hm3]
    field_simp <;> ring

#print axioms shiftedProduct_factorization
#print axioms characteristic_coefficients_from_spectrum
#print axioms normalized_characteristic_coefficients_from_spectrum

end UnicyclicProduct
