module
public import MathAndTheory.Mathematics.DomiRank.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

@[expose] public section

namespace MathAndTheory.DomiRank

open Matrix Finset

/-- Degree--log-degree covariance over uniformly oriented edges, in nats.
This is the equivalent vertex-sum formula in Proposition 4.4 of the source. -/
noncomputable def degreeLogCovarianceNats : ℝ :=
  (∑ i : Fin 14, (A *ᵥ degree) i * Real.log (degree i)) / (∑ i : Fin 14, degree i) -
  ((∑ i : Fin 14, degree i ^ 2) / (∑ i : Fin 14, degree i) ^ 2) *
    (∑ i : Fin 14, degree i * Real.log (degree i))

/-- The covariance in the paper uses base-two logarithms. -/
noncomputable def degreeLogCovarianceBits : ℝ := degreeLogCovarianceNats / Real.log 2

/-- The exact covariance for this graph. -/
theorem degreeLogCovarianceNats_eq :
    degreeLogCovarianceNats =
      (159 * Real.log 5 - 153 * Real.log 7 - 120 * Real.log 2) / 512 := by
  unfold degreeLogCovarianceNats
  rw [degree_eq]
  norm_num [A, adjData, Matrix.map_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Real.log_one]
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow] <;> norm_num
  rw [h8]
  ring

/-- Strictly negative covariance; only monotonicity and the power law of log are used. -/
theorem degreeLogCovarianceNats_neg : degreeLogCovarianceNats < 0 := by
  rw [degreeLogCovarianceNats_eq]
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h57 : Real.log (5 : ℝ) ≤ Real.log 7 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h78 : Real.log (7 : ℝ) < 3 * Real.log 2 := by
    have h : Real.log (7 : ℝ) < Real.log 8 := Real.log_lt_log (by norm_num) (by norm_num)
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow] <;> norm_num
    rwa [h8] at h
  apply div_neg_of_neg_of_pos _ (by norm_num)
  linarith

theorem degreeLogCovarianceBits_neg : degreeLogCovarianceBits < 0 := by
  exact div_neg_of_neg_of_pos degreeLogCovarianceNats_neg (Real.log_pos (by norm_num))

end MathAndTheory.DomiRank
