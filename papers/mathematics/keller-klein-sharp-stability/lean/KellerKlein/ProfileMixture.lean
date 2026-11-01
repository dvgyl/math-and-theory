import KellerKlein.Envelopes
import KellerKlein.KernelMeasurability

open MeasureTheory Set
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace KellerKlein

noncomputable section

lemma cosineProfile_rpow_weight (b t : ℝ) :
    cosineProfile b t ^ (b ^ 2) = |Real.cos (b * t)| := by
  by_cases hb : b = 0
  · simp [cosineProfile, hb]
  · rw [cosineProfile, ← Real.rpow_mul (abs_nonneg _)]
    rw [one_div_mul_cancel (pow_ne_zero 2 hb), Real.rpow_one]

/-- Pointwise weighted AM--GM converts the actual product into scalar profiles.
Zero coefficients have zero weight and require no special assumption. -/
theorem abs_cosProduct_le_profile_mixture {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (hvar : ∑ i ∈ S, c i ^ 2 = 1) (t : ℝ) :
    |cosProduct S c t| ≤ ∑ i ∈ S, c i ^ 2 * cosineProfile (c i) t := by
  have hm := Real.geom_mean_le_arith_mean_weighted S (fun i => c i ^ 2)
    (fun i => cosineProfile (c i) t) (fun i hi => sq_nonneg _) hvar
    (fun i hi => Real.rpow_nonneg (abs_nonneg _) _)
  simpa only [cosineProfile_rpow_weight, cosProduct, Finset.abs_prod] using hm

/-- A direct reduction from the normalized cosine product to uniformly bounded
one-variable profile integrals.  This uses weighted AM--GM, not a supremum or
an equal-coefficient reduction. -/
theorem integral_cosProduct_le_uniform_profile {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (hvar : ∑ i ∈ S, c i ^ 2 = 1) (k : ℝ → ℝ) (T B : ℝ)
    (hk : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ k u)
    (hi : IntervalIntegrable (fun u => k u * cosProduct S c (T * u)) volume 0 1)
    (hp : ∀ i ∈ S, IntervalIntegrable
      (fun u => k u * cosineProfile (c i) (T * u)) volume 0 1)
    (hB : ∀ i ∈ S, c i ≠ 0 →
      (∫ u in (0 : ℝ)..1, k u * cosineProfile (c i) (T * u)) ≤ B) :
    (∫ u in (0 : ℝ)..1, k u * cosProduct S c (T * u)) ≤ B := by
  have hsum : IntervalIntegrable
      (fun u => ∑ i ∈ S, c i ^ 2 * (k u * cosineProfile (c i) (T * u))) volume 0 1 := by
    have hh := IntervalIntegrable.sum S
      (f := fun i u => c i ^ 2 * (k u * cosineProfile (c i) (T * u)))
      (fun i hi => (hp i hi).const_mul (c i ^ 2))
    have heq : (∑ i ∈ S, fun u => c i ^ 2 * (k u * cosineProfile (c i) (T * u))) =
        (fun u => ∑ i ∈ S, c i ^ 2 * (k u * cosineProfile (c i) (T * u))) := by
      funext u
      simp only [Finset.sum_apply]
    rw [heq] at hh
    exact hh
  calc
    (∫ u in (0 : ℝ)..1, k u * cosProduct S c (T * u)) ≤
        ∫ u in (0 : ℝ)..1, ∑ i ∈ S, c i ^ 2 * (k u * cosineProfile (c i) (T * u)) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi hsum
      intro u hu
      have h := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (abs_cosProduct_le_profile_mixture S c hvar (T * u))) (hk u hu)
      calc
        k u * cosProduct S c (T * u) ≤ k u * ∑ i ∈ S, c i ^ 2 * cosineProfile (c i) (T * u) := h
        _ = ∑ i ∈ S, c i ^ 2 * (k u * cosineProfile (c i) (T * u)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ i ∈ S, c i ^ 2 *
        (∫ u in (0 : ℝ)..1, k u * cosineProfile (c i) (T * u)) := by
      rw [intervalIntegral.integral_finset_sum (fun i hi => (hp i hi).const_mul (c i ^ 2))]
      simp only [intervalIntegral.integral_const_mul]
    _ ≤ ∑ i ∈ S, c i ^ 2 * B := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : c i = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hB i hi hz) (sq_nonneg _)
    _ = B := by rw [← Finset.sum_mul, hvar, one_mul]

end

end KellerKlein
