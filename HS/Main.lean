module
public import HS.Certificate
public import HS.Purity
public import HS.Spectral
public import HS.Entropy
public import HS.MarginalSpectrum

@[expose] public section

open scoped BigOperators

set_option autoImplicit false

namespace HS

/-- Von Neumann entropy, with natural logarithms, of a balanced marginal.
The eigenvalues are those of the actual complex Gram matrix of the flattening.
Lean's convention `Real.log 0 = 0` gives the usual value `0 log 0 = 0`. -/
noncomputable def cutEntropy (cut : Fin 3) (z : Fin 16 → ℂ) : ℝ :=
  ∑ i, -(cutEigenvalues cut z i) * Real.log (cutEigenvalues cut z i)

/-- Average over AB|CD, AC|BD, and AD|BC. -/
noncomputable def averageEntropy (z : Fin 16 → ℂ) : ℝ :=
  (∑ cut : Fin 3, cutEntropy cut z) / 3

/-- The third elementary symmetric function bound, stated directly in terms
of the eigenvalues of the actual three reduced matrices. -/
theorem third_elementary_bound (z : Fin 16 → ℂ) :
    (∑ cut : Fin 3, elementaryThree (cutEigenvalues cut z)) ≤
      (5 / 36 : ℝ) * stateNormSq z ^ 3 := by
  rw [elementaryThree_sum_eq_minorSum]
  exact minorSum_le z

/-- Equality in the third elementary symmetric function bound. -/
theorem hsState_third_elementary :
    (∑ cut : Fin 3, elementaryThree (cutEigenvalues cut hsState)) = (5 / 36 : ℝ) := by
  rw [elementaryThree_sum_eq_minorSum]
  exact hsState_minorSum

/-- The exact maximum of the summed third elementary symmetric functions
over every normalized four-qubit pure state. -/
theorem third_elementary_maximum :
    IsGreatest
      ((fun z : Fin 16 → ℂ => ∑ cut : Fin 3, elementaryThree (cutEigenvalues cut z)) ''
        {z : Fin 16 → ℂ | stateNormSq z = 1})
      (5 / 36 : ℝ) := by
  constructor
  · exact ⟨hsState, hsState_normalized, hsState_third_elementary⟩
  · rintro value ⟨z, hn, rfl⟩
    change stateNormSq z = 1 at hn
    simpa [hn] using third_elementary_bound z

/-- Homogeneous moment inequality on every complex four-qubit vector. -/
theorem homogeneous_moment_bound (z : Fin 16 → ℂ) :
    12 * (∑ cut : Fin 3, ∑ i : Fin 4, cutEigenvalues cut z i ^ 3) +
      13 * stateNormSq z ^ 3 ≤ 18 * stateNormSq z * puritySum z := by
  have hm := minorSum_le z
  have hi := total_moment_identity z
  linarith

/-- The unrestricted Higuchi--Sudbery upper bound.
Normalization is the only hypothesis on the sixteen complex amplitudes. -/
theorem higuchi_sudbery_bound (z : Fin 16 → ℂ) (hn : stateNormSq z = 1) :
    averageEntropy z ≤ Real.log 2 + Real.log 3 / 2 := by
  apply entropy_sum_le (cutEigenvalues · z)
  · exact fun cut i => cutEigenvalues_nonneg cut z i
  · intro cut
    rw [cutEigenvalues_sum, hn]
  · rw [cutEigenvalues_square_sum]
    exact puritySum_lower_normalized z hn
  · exact cubic_moment_bound z hn (minorSum_le_of_normalized z hn)

/-- The explicit Higuchi--Sudbery state attains the upper bound. -/
theorem hsState_averageEntropy :
    averageEntropy hsState = Real.log 2 + Real.log 3 / 2 :=
  hsState_entropy

/-- The exact global maximum over all normalized four-qubit pure states. -/
theorem higuchi_sudbery_maximum :
    IsGreatest (averageEntropy '' {z : Fin 16 → ℂ | stateNormSq z = 1})
      (Real.log 2 + Real.log 3 / 2) := by
  constructor
  · exact ⟨hsState, hsState_normalized, hsState_averageEntropy⟩
  · rintro value ⟨z, hn, rfl⟩
    exact higuchi_sudbery_bound z hn

/-- The same upper bound expressed in bits. -/
theorem higuchi_sudbery_bound_bits (z : Fin 16 → ℂ) (hn : stateNormSq z = 1) :
    averageEntropy z / Real.log 2 ≤ 1 + Real.log 3 / (2 * Real.log 2) := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right (higuchi_sudbery_bound z hn) hp.le
  convert h using 1
  field_simp [hp.ne']

end HS
