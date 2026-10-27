import SixGapMarginGeometry
namespace SixCertificates
open MathAndTheory.Gyires.CirculantCertificate

theorem gaps_zero_of_power_sum_zero (g : Fin 6 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (h : gapPowerSum g = 0) : ∀ i, i ≠ 0 → g i = 0 := by
  have h1 : 0 ≤ g 1 ^ 12 := pow_nonneg (hg 1) _
  have h2 : 0 ≤ g 2 ^ 12 := pow_nonneg (hg 2) _
  have h3 : 0 ≤ g 3 ^ 12 := pow_nonneg (hg 3) _
  have h4 : 0 ≤ g 4 ^ 12 := pow_nonneg (hg 4) _
  have h5 : 0 ≤ g 5 ^ 12 := pow_nonneg (hg 5) _
  unfold gapPowerSum at h
  have h1' : g 1 ^ 12 = 0 := by linarith
  have h2' : g 2 ^ 12 = 0 := by linarith
  have h3' : g 3 ^ 12 = 0 := by linarith
  have h4' : g 4 ^ 12 = 0 := by linarith
  have h5' : g 5 ^ 12 = 0 := by linarith
  have z1 : g 1 = 0 := eq_zero_of_pow_eq_zero h1'
  have z2 : g 2 = 0 := eq_zero_of_pow_eq_zero h2'
  have z3 : g 3 = 0 := eq_zero_of_pow_eq_zero h3'
  have z4 : g 4 = 0 := eq_zero_of_pow_eq_zero h4'
  have z5 : g 5 = 0 := eq_zero_of_pow_eq_zero h5'
  intro i hi
  fin_cases i <;> simp_all

theorem gapWeights_constant_of_zero (σ : Equiv.Perm (Fin 6)) (g : Fin 6 → ℝ)
    (hg : ∀ i, i ≠ 0 → g i = 0) : gapWeights σ g = fun _ => g 0 := by
  funext i
  unfold gapWeights
  rw [Finset.sum_eq_single 0]
  · intro j _ hj
    exact hg j hj
  · intro h0
    exact False.elim (h0 (by simp))
end SixCertificates
