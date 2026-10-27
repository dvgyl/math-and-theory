import SixSharpness
import SixNormalization
namespace MathAndTheory.Gyires.CirculantSix
open MathAndTheory.Gyires.CirculantCertificate
open SixCertificates

noncomputable def normalizedSharpWeights : Fin 6 → ℝ := ![0, 0, 0, 0, 1 / 2, 1 / 2]
noncomputable def normalizedSharpGaps : Fin 6 → ℝ := ![0, 0, 0, 0, 1 / 2, 0]

theorem normalized_sharp_sum : ∑ i, normalizedSharpWeights i = 1 := by
  norm_num [normalizedSharpWeights, Fin.sum_univ_succ]

theorem normalized_sharp_nonneg : ∀ i, 0 ≤ normalizedSharpWeights i := by
  intro i
  fin_cases i <;> norm_num [normalizedSharpWeights]

theorem normalized_sharp_stochastic :
    matrix normalizedSharpWeights ∈ doublyStochastic ℝ (Fin 6) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => normalized_sharp_nonneg (j - i), ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [matrix, normalizedSharpWeights, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [matrix, normalizedSharpWeights, Fin.sum_univ_succ]

theorem normalized_sharp_deficit :
    324 * (matrix normalizedSharpWeights).permanent ^ 2 -
      5 * (matrix normalizedSharpWeights * (matrix normalizedSharpWeights).transpose).permanent =
      37 / 512 := by
  change 324 * (circulant normalizedSharpWeights).permanent ^ 2 -
    5 * (circulant normalizedSharpWeights * (circulant normalizedSharpWeights).transpose).permanent = _
  rw [permanent_formula, RawSix.matrix_gram, permanent_formula]
  norm_num [normalizedSharpWeights, RawSix.P6, RawSix.gram6]

theorem normalized_sharp_gapWeights :
    gapWeights (Equiv.refl _) normalizedSharpGaps = normalizedSharpWeights := by
  rw [← prefix_identity]
  funext i
  fin_cases i <;> norm_num [prefixVector, normalizedSharpGaps, normalizedSharpWeights]

theorem normalized_margin_coefficient_le (K : ℝ)
    (hK : ∀ (g : Fin 6 → ℝ), (∀ i, 0 ≤ g i) →
      matrix (gapWeights (Equiv.refl _) g) ∈ doublyStochastic ℝ (Fin 6) →
      K * gapPowerSum g ≤
        324 * (matrix (gapWeights (Equiv.refl _) g)).permanent ^ 2 -
          5 * (matrix (gapWeights (Equiv.refl _) g) *
            (matrix (gapWeights (Equiv.refl _) g)).transpose).permanent) : K ≤ 296 := by
  have hg : ∀ i, 0 ≤ normalizedSharpGaps i := by
    intro i
    fin_cases i <;> norm_num [normalizedSharpGaps]
  have hs : matrix (gapWeights (Equiv.refl _) normalizedSharpGaps) ∈ doublyStochastic ℝ (Fin 6) := by
    rw [normalized_sharp_gapWeights]
    exact normalized_sharp_stochastic
  have h := hK normalizedSharpGaps hg hs
  rw [normalized_sharp_gapWeights, normalized_sharp_deficit] at h
  norm_num [gapPowerSum, normalizedSharpGaps] at h
  linarith

#print axioms normalized_sharp_stochastic
#print axioms normalized_sharp_deficit
#print axioms normalized_margin_coefficient_le
end MathAndTheory.Gyires.CirculantSix
