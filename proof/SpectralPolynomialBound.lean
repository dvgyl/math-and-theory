module
public import SpectralMomentBound
public import SpectralCoefficients
public import CumulantAlgebra

@[expose] public section

/-!
The characteristic-polynomial bound, with a positive spectral shift and the
thermodynamic uncertainty inequality explicit as hypotheses. This is not yet
the arbitrary-rate Markov theorem: the separate matrix and corrector modules
must supply these hypotheses from rates before that conclusion can be claimed.
-/
namespace UnicyclicPolynomial
noncomputable section
open scoped BigOperators
open Polynomial UnicyclicCumulant
set_option maxHeartbeats 2000000

theorem bound_from_spectral_shift_and_uncertainty {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (theta : ι → ℝ)
    (P : Polynomial ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hth : ∀ i ∈ s, 0 < theta i)
    (hd : (a-b)^2 = ∏ i ∈ s, theta i)
    (hfactor : P+C ((a-b)^2) = UnicyclicProduct.shiftedProduct s theta)
    (htur : 1/Real.log (a/b) ≤
      second (P.coeff 1) (P.coeff 2) (a^2) (b^2) /
        first (P.coeff 1) (a^2) (b^2)) :
    -(1/16 : ℝ) ≤
      third (P.coeff 1) (P.coeff 2) (P.coeff 3) (a^2) (b^2) /
        first (P.coeff 1) (a^2) (b^2) ∧
      third (P.coeff 1) (P.coeff 2) (P.coeff 3) (a^2) (b^2) /
        first (P.coeff 1) (a^2) (b^2) ≤ 1 := by
  let T := ∑ i ∈ s, 1/theta i
  have hT : 0 < T := Finset.sum_pos (fun i hi => one_div_pos.mpr (hth i hi)) hs
  let x := fun i => (1/theta i)/T
  let p2 := ∑ i ∈ s, (x i)^2
  let p3 := ∑ i ∈ s, (x i)^3
  let d := (a-b)^2
  let c := (a+b)/(a-b)
  let r := (a-b)/(a+b)
  have hab : 0 < a+b := by linarith
  have hdiff : 0 < a-b := sub_pos.mpr hba
  have hd0 : d ≠ 0 := ne_of_gt (sq_pos_of_pos hdiff)
  have hc0 : c ≠ 0 := div_ne_zero (ne_of_gt hab) (ne_of_gt hdiff)
  have hr0 : 0 < r := div_pos hdiff hab
  have hr1 : r < 1 := by
    apply (div_lt_one hab).mpr
    linarith
  have hcr : c = 1/r := by
    dsimp [c,r]
    field_simp
  have hx : ∀ i ∈ s, 0 ≤ x i := by
    intro i hi
    exact le_of_lt (div_pos (one_div_pos.mpr (hth i hi)) hT)
  have hsum : ∑ i ∈ s, x i = 1 := by
    dsimp [x]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hT)
  obtain ⟨ha1,ha2,ha3⟩ := UnicyclicProduct.normalized_characteristic_coefficients_from_spectrum
    s theta P d T (fun i hi => ne_of_gt (hth i hi)) hd hfactor rfl (ne_of_gt hT)
  have hminus : a^2-b^2 = d*c := by
    dsimp [d,c]
    field_simp
    ring
  have hplus : a^2+b^2 = d*(c^2+1)/2 := by
    dsimp [d,c]
    field_simp
    ring
  obtain ⟨hF,hS⟩ := explicit_cumulant_ratio_reduction
    (P.coeff 1) (P.coeff 2) (P.coeff 3) (a^2) (b^2) d T c p2 p3
    hd0 (ne_of_gt hT) hc0 ha1 ha2 ha3 hminus hplus
  have hF' : c*p2-(c^2-1)/(2*c) = (p2-(1-r^2)/2)/r := by
    rw [hcr]
    field_simp [ne_of_gt hr0]
    ring
  rw [hF,hF'] at htur
  have heq : (1+r)/(1-r) = a/b := by
    apply (div_eq_div_iff (ne_of_gt (sub_pos.mpr hr1)) (ne_of_gt hb)).mpr
    dsimp [r]
    field_simp
    ring
  have htur' : (1-r^2)/2+r/Real.log ((1+r)/(1-r)) ≤ p2 := by
    rw [heq]
    have h := (le_div_iff₀ hr0).mp htur
    have he : 1/Real.log (a/b)*r = r/Real.log (a/b) := by ring
    rw [he] at h
    nlinarith only [h]
  have hbounds := UnicyclicMoments.spectral_skewness_interval s x r hr0 hr1 hx hsum htur'
  have hS' : c^2*(3*p2^2-2*p3)+(c^2-1)*(1-3*p2)/2 =
      UnicyclicMoments.skewness p2 p3 r := by
    rw [hcr]
    dsimp [UnicyclicMoments.skewness]
    field_simp [ne_of_gt hr0]
    ring
  rw [hS,hS']
  exact hbounds

#print axioms bound_from_spectral_shift_and_uncertainty
end
end UnicyclicPolynomial
