import QPermanentResearch.PotentialGap
import Mathlib.Analysis.Complex.Basic

/-!
The quantitative potential bound for actual complex unit coordinates.
All modulus and triangle conditions in PotentialGap are proved here.
The identification of this explicit expression with a sphere integral is
not part of this module.
-/

namespace QPermanentResearch

noncomputable def scaledSpherePotential (τ : ℝ) (z₀ z₁ z₂ : ℂ) : ℝ :=
  let Q := ‖z₀‖^2+‖z₁‖^2+τ^2*‖z₂‖^2
  Real.log ((Q+Real.sqrt (Q^2-‖(2:ℂ)*z₀*z₁+(τ:ℂ)^2*z₂^2‖^2))/2)

theorem scaledSpherePotential_outside_caps {τ ρ : ℝ} (z₀ z₁ z₂ : ℂ)
    (hunit : ‖z₀‖^2+‖z₁‖^2+‖z₂‖^2=1)
    (hτ : 0 < τ) (hτone : τ ≤ 1)
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hcap₀ : ‖z₀‖^2 ≤ 1-ρ^2) (hcap₁ : ‖z₁‖^2 ≤ 1-ρ^2) :
    scaledSpherePotential τ z₀ z₁ z₂ ≤
      -(min ((1-τ^2)/2) (1/16))*ρ^2 := by
  have hτsq : τ^2 ≤ 1 := by nlinarith
  have hnormX : ‖(2:ℂ)*z₀*z₁‖ = 2*‖z₀‖*‖z₁‖ := by simp [norm_mul]
  have hnormY : ‖(τ:ℂ)^2*z₂^2‖ = τ^2*‖z₂‖^2 := by
    simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hupper := norm_add_le ((2:ℂ)*z₀*z₁) ((τ:ℂ)^2*z₂^2)
  rw [hnormX, hnormY] at hupper
  have hsQ : ‖(2:ℂ)*z₀*z₁+(τ:ℂ)^2*z₂^2‖ ≤
      ‖z₀‖^2+‖z₁‖^2+τ^2*‖z₂‖^2 := by
    nlinarith only [hupper, sq_nonneg (‖z₀‖-‖z₁‖)]
  have hreverse := norm_sub_le ((2:ℂ)*z₀*z₁+(τ:ℂ)^2*z₂^2) ((τ:ℂ)^2*z₂^2)
  simp only [add_sub_cancel_right, hnormX, hnormY] at hreverse
  have hsqrt : Real.sqrt (‖z₀‖^2*‖z₁‖^2) = ‖z₀‖*‖z₁‖ := by
    rw [Real.sqrt_mul (sq_nonneg ‖z₀‖), Real.sqrt_sq (norm_nonneg z₀),
      Real.sqrt_sq (norm_nonneg z₁)]
  have hLower : 2*Real.sqrt (‖z₀‖^2*‖z₁‖^2)-τ^2*‖z₂‖^2 ≤
      ‖(2:ℂ)*z₀*z₁+(τ:ℂ)^2*z₂^2‖ := by
    rw [hsqrt]
    linarith
  have hmul₀ := mul_le_mul_of_nonneg_right hτsq (sq_nonneg ‖z₀‖)
  have hmul₁ := mul_le_mul_of_nonneg_right hτsq (sq_nonneg ‖z₁‖)
  have hQlower : τ^2*(‖z₀‖^2+‖z₁‖^2+‖z₂‖^2) ≤
      ‖z₀‖^2+‖z₁‖^2+τ^2*‖z₂‖^2 := by
    nlinarith only [hmul₀, hmul₁]
  rw [hunit, mul_one] at hQlower
  have hQ : 0 < ‖z₀‖^2+‖z₁‖^2+τ^2*‖z₂‖^2 :=
    lt_of_lt_of_le (sq_pos_of_pos hτ) hQlower
  unfold scaledSpherePotential
  exact closed_potential_outside_caps (sq_nonneg ‖z₀‖) (sq_nonneg ‖z₁‖)
    (sq_nonneg ‖z₂‖) hunit hρ hρhalf hcap₀ hcap₁ hτsq rfl hQ
    (norm_nonneg _) hsQ hLower

#print axioms scaledSpherePotential_outside_caps

end QPermanentResearch
