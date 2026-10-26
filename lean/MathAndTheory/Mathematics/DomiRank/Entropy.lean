module
public import MathAndTheory.Mathematics.DomiRank.Scores
public import MathAndTheory.Mathematics.DomiRank.EntropyBounds

@[expose] public section

namespace MathAndTheory.DomiRank

noncomputable section

/-- Shannon entropy of the normalized distribution, using natural logarithms. -/
def entropyNats (s : ℝ) : ℝ :=
  -(∑ i : Fin 14, distribution s i * Real.log (distribution s i))

/-- Shannon entropy in bits, as in the original conjecture. -/
def entropyBits (s : ℝ) : ℝ := entropyNats s / Real.log 2

/-- The optional normalization by log₂ of the graph order. -/
def normalizedEntropy (s : ℝ) : ℝ := entropyNats s / Real.log 14

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

theorem entropyNats_left : entropyNats sigmaLeft = leftEntropyNats := by
  norm_num [entropyNats, distribution_eq_left, vertexClass, leftProbability,
    Fin.sum_univ_succ, leftEntropyNats] <;> ring

theorem entropyNats_right : entropyNats sigmaRight = rightEntropyNats := by
  norm_num [entropyNats, distribution_eq_right, vertexClass, rightProbability,
    Fin.sum_univ_succ, rightEntropyNats] <;> ring

/-- A strict rational gap, not a floating-point comparison. -/
theorem entropyNats_gap :
    entropyNats sigmaLeft + (1 : ℝ) / 10000 < entropyNats sigmaRight := by
  rw [entropyNats_left, entropyNats_right]
  exact entropyNats_certificate

theorem entropyBits_strict_increase : entropyBits sigmaLeft < entropyBits sigmaRight := by
  apply div_lt_div_of_pos_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have h := entropyNats_gap
  linarith

theorem normalizedEntropy_strict_increase :
    normalizedEntropy sigmaLeft < normalizedEntropy sigmaRight := by
  apply div_lt_div_of_pos_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 14))
  have h := entropyNats_gap
  linarith

end
end MathAndTheory.DomiRank
