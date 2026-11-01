import KellerKlein.ZoneAProfile

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace KellerKlein.ZoneA

def primaryCoeff (a b ξ : ℝ) : Fin 9 → ℝ :=
  ![1 + ξ, -a / Real.pi, -(A ξ) * a ^ 2, B ξ * a ^ 3,
    C ξ * a ^ 4 - b ^ 2 * (1 + ξ) / 12,
    b ^ 2 * a / (12 * Real.pi), b ^ 2 * AL ξ * a ^ 2 / 12,
    D ξ * a ^ 7, b ^ 4 * (1 + ξ) / 288]

lemma primaryPolynomial_sum (a b ξ s : ℝ) :
    gaussian s * primaryPolynomial a b ξ s =
      ∑ i : Fin 9, primaryCoeff a b ξ i * (s ^ (i : ℕ) * gaussian s) := by
  simp [primaryCoeff, Fin.sum_univ_succ, primaryPolynomial, upperPoly, lowerPoly]
  ring

lemma integrable_primaryPolynomial (a b ξ : ℝ) :
    IntegrableOn (fun s => gaussian s * primaryPolynomial a b ξ s) (Ioi 0) := by
  have h : IntegrableOn (fun s => ∑ i : Fin 9,
      primaryCoeff a b ξ i * (s ^ (i : ℕ) * gaussian s)) (Ioi 0) := by
    apply integrable_finset_sum
    intro i hi
    exact (integrableOn_pow_gaussian (i : ℕ)).const_mul _
  simpa only [← primaryPolynomial_sum] using h

lemma integral_primaryPolynomial_moments (a b ξ : ℝ) :
    (∫ s in Ioi (0 : ℝ), gaussian s * primaryPolynomial a b ξ s) =
      ∑ i : Fin 9, primaryCoeff a b ξ i * halfMoment (i : ℕ) := by
  simp_rw [primaryPolynomial_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    rfl
  · intro i hi
    exact (integrableOn_pow_gaussian (i : ℕ)).const_mul _

def primaryValue (a b ξ : ℝ) : ℝ :=
  phi0 * a * (1 + ξ) - a ^ 2 / Real.pi ^ 2 - phi0 * A ξ * a ^ 3 +
    (2 * B ξ / Real.pi) * a ^ 4 + 3 * phi0 * C ξ * a ^ 5 +
    (48 * D ξ / Real.pi) * a ^ 8 - phi0 * b ^ 2 * a * (1 + ξ) / 4 +
    2 * b ^ 2 * a ^ 2 / (3 * Real.pi ^ 2) +
    5 * phi0 * AL ξ * b ^ 2 * a ^ 3 / 4 +
    35 * phi0 * (1 + ξ) * b ^ 4 * a / 96

lemma integral_primaryPolynomial_eq (a b ξ : ℝ) :
    a / Real.pi * (∫ s in Ioi (0 : ℝ), gaussian s * primaryPolynomial a b ξ s) =
      primaryValue a b ξ := by
  rw [integral_primaryPolynomial_moments]
  simp [primaryCoeff, Fin.sum_univ_succ, halfMoment_zero, halfMoment_one,
    halfMoment_two, halfMoment_three, halfMoment_four, halfMoment_five,
    halfMoment_six, halfMoment_seven, halfMoment_eight, primaryValue]
  field_simp [Real.pi_ne_zero]
  ring

end KellerKlein.ZoneA
