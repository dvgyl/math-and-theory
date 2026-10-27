import SixMargin
import SixChamberGeometry
namespace SixCertificates
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem gapPowerSum_eq_sum_sub (g : Fin 6 → ℝ) :
    gapPowerSum g = (∑ i, g i ^ 12) - g 0 ^ 12 := by
  simp [gapPowerSum, Fin.sum_univ_succ]
  ring

theorem gapPowerSum_permutation (ρ : Equiv.Perm (Fin 6)) (hρ : ρ 0 = 0)
    (g : Fin 6 → ℝ) : gapPowerSum (g ∘ ρ.symm) = gapPowerSum g := by
  have hz : ρ.symm 0 = 0 := by apply ρ.injective; simp [hρ]
  rw [gapPowerSum_eq_sum_sub, gapPowerSum_eq_sum_sub]
  simp only [Function.comp_apply, hz]
  congr 1
  exact Equiv.sum_comp ρ.symm (fun i => g i ^ 12)

theorem representative_zero : ∀ r, AffineCoverSix.representative r 0 = 0 := by
  decide +kernel

theorem gapPowerSum_nonneg (g : Fin 6 → ℝ) : 0 ≤ gapPowerSum g := by
  unfold gapPowerSum
  positivity
end SixCertificates
