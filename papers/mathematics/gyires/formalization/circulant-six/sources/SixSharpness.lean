import SixRawDeficitBridge
import SixMargin
import SixChamberGeometry
namespace MathAndTheory.Gyires.CirculantSix
open MathAndTheory.Gyires.CirculantCertificate
open SixCertificates

def sharpWeights : Fin 6 → ℝ := ![0, 0, 0, 0, 1, 1]
def sharpGaps : Fin 6 → ℝ := ![0, 0, 0, 0, 1, 0]

theorem sharp_gap_sum : gapPowerSum sharpGaps = 1 := by norm_num [gapPowerSum, sharpGaps]

theorem sharp_deficit :
    324 * (circulant sharpWeights).permanent ^ 2 -
      5 * (circulant sharpWeights * (circulant sharpWeights).transpose).permanent = 296 := by
  rw [permanent_formula, RawSix.matrix_gram, permanent_formula]
  norm_num [sharpWeights, RawSix.P6, RawSix.gram6]

theorem strong_equality_constant (c : ℝ) :
    324 * (circulant (fun _ : Fin 6 => c)).permanent ^ 2 =
      5 * (circulant (fun _ : Fin 6 => c) * (circulant (fun _ : Fin 6 => c)).transpose).permanent := by
  rw [permanent_formula, RawSix.matrix_gram, permanent_formula]
  norm_num [RawSix.P6, RawSix.gram6]
  ring
theorem sharp_gapWeights : gapWeights (Equiv.refl _) sharpGaps = sharpWeights := by
  rw [← prefix_identity]
  funext i
  fin_cases i <;> norm_num [prefixVector, sharpGaps, sharpWeights]

theorem margin_coefficient_le (K : ℝ)
    (hK : ∀ (g : Fin 6 → ℝ), (∀ i, 0 ≤ g i) →
      K * gapPowerSum g ≤
        324 * (circulant (gapWeights (Equiv.refl _) g)).permanent ^ 2 -
          5 * (circulant (gapWeights (Equiv.refl _) g) *
            (circulant (gapWeights (Equiv.refl _) g)).transpose).permanent) : K ≤ 296 := by
  have hg : ∀ i, 0 ≤ sharpGaps i := by intro i; fin_cases i <;> norm_num [sharpGaps]
  have h := hK sharpGaps hg
  simpa only [sharp_gap_sum, mul_one, sharp_gapWeights, sharp_deficit] using h

#print axioms sharp_deficit
#print axioms strong_equality_constant
#print axioms margin_coefficient_le
end MathAndTheory.Gyires.CirculantSix
