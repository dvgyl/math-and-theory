import KellerKlein.ZoneBTheorem
import KellerKlein.SignedRademacher
import KellerKlein.NormalCDF

/-!
# The missing small-coefficient concentration half

These theorems concern the actual uniform Rademacher sum with arbitrary
signed real coefficients.  The only assumptions are normalization, the
coefficient bound, and the stated parameter ranges.  Prawitz's inequality,
the characteristic-function envelopes, all integral estimates and their
numeric constants are proved in the imported dependency chain.

The second theorem uses Mathlib's CDF of the probability measure N(0,1).
It is the upper CDF discrepancy for nonnegative locations.  It does not
claim the opposite discrepancy or the large-coefficient ranges.
-/

open scoped BigOperators

namespace KellerKlein

/-- The genuine closed concentration inequality, for every finite normalized
signed coefficient vector with maximum magnitude at most 0.07. -/
theorem small_coefficient_upper_concentration {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7 / 100)
    (hca : ∀ i, |coeff i| ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1) (hx : 0 ≤ x) :
    rademacherConcentration coeff x ≤ H a + H x := by
  rw [rademacherConcentration_abs coeff x]
  apply rademacher_concentration_small_max (fun i => |coeff i|) ha haMax
    (fun i => abs_nonneg _) hca
  · simpa only [sq_abs] using hvar
  · exact hx

/-- The same concentration theorem written directly in terms of the standard
normal probability CDF. -/
theorem small_coefficient_upper_concentration_normal {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7 / 100)
    (hca : ∀ i, |coeff i| ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1) (hx : 0 ≤ x) :
    rademacherConcentration coeff x ≤
      2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x +
        2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a - 2 := by
  have h := small_coefficient_upper_concentration coeff ha haMax hca hvar hx
  rw [standardNormal_cdf_eq, standardNormal_cdf_eq]
  unfold H at h
  linarith

/-- The missing upper CDF discrepancy bound, for the actual finite sum and
Mathlib's actual standard-normal probability measure. -/
theorem small_coefficient_upper_cdf {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7 / 100)
    (hca : ∀ i, |coeff i| ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1) (hx : 0 ≤ x) :
    rademacherCDF coeff x - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x ≤
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a - 1 / 2 := by
  have hv : ∑ i, |coeff i| ^ 2 = 1 := by simpa only [sq_abs] using hvar
  have h := rademacherCDF_small_max_nonneg (fun i => |coeff i|) ha haMax
    (fun i => abs_nonneg _) hca hv hx
  rw [rademacherCDF_abs coeff x, standardNormal_cdf_eq, standardNormal_cdf_eq]
  linarith

end KellerKlein
