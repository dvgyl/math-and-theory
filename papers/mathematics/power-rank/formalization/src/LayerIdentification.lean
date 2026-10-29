import BivariateCoefficients

noncomputable section
open Polynomial
namespace PowerRank

/-- The literal coefficient polynomial in Z, extracted from F^M. -/
def actualLayerPolynomial (M j k : ℕ) : ℚ[X] :=
  ∑ c ∈ Finset.range (M + 1),
    monomial c (((actualGenerator ^ M).coeff (biIndex j c)).coeff k)

theorem actualLayerPolynomial_coeff (M j k c : ℕ) :
    (actualLayerPolynomial M j k).coeff c =
      if c ≤ M then ((actualGenerator ^ M).coeff (biIndex j c)).coeff k else 0 := by
  classical
  simp [actualLayerPolynomial, finsetSum_coeff, coeff_monomial]

/-- Every coefficient of the explicit layer is the literal F^M coefficient. -/
theorem layerPolynomial_coeff_eq_actual (M j k c : ℕ) (hjM : j ≤ 2 * M) :
    (layerPolynomial M j k).coeff c =
      ((actualGenerator ^ M).coeff (biIndex j c)).coeff k := by
  rw [layerPolynomial_coeff]
  by_cases hvalid : j - M ≤ c ∧ c ≤ j / 2
  · rw [ite_eq_left hvalid]
    symm
    exact actualGenerator_pow_coeff_X M j c k (by omega) (by omega) (by omega)
  · rw [ite_eq_right hvalid, actualGenerator, trinomialGenerator_pow_coeff,
      ite_eq_right (by omega), coeff_zero]

/-- The previously checked layer polynomial is exactly the original power's
coefficient polynomial. No expansion hypothesis is assumed. -/
theorem actualLayerPolynomial_eq_layerPolynomial (M j k : ℕ) (hjM : j ≤ 2 * M) :
    actualLayerPolynomial M j k = layerPolynomial M j k := by
  ext c
  rw [actualLayerPolynomial_coeff]
  by_cases hc : c ≤ M
  · rw [ite_eq_left hc, layerPolynomial_coeff_eq_actual M j k c hjM]
  · rw [ite_eq_right hc, layerPolynomial_coeff, ite_eq_right (by omega)]

end PowerRank
