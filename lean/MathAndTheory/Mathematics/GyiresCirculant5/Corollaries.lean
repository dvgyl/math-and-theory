module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Theorems
public import MathAndTheory.Mathematics.GyiresCirculant5.Normalization

/-!
# The normalized ratio

For weights that are nonnegative and sum to one, Gyires's ratio is at least `24/625 = 5!/5⁵`
(`normalizedGyiresRatio`), with equality exactly at the uniform weights
(`normalizedGyiresRatio_eq_iff`).
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MathAndTheory.GyiresCirculant5

open scoped BigOperators

theorem normalizedGyiresRatio (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (24 : ℝ) / 625 ≤ 4 * (circ w).permanent^2 / gyiresDenominator w := by
  have hd := positiveDenominator w hw hsum
  apply (le_div_iff₀ hd).mpr
  have h := gyires_matrix_inequality w hw
  change 24 * gyiresDenominator w ≤ 2500 * (circ w).permanent^2 at h
  nlinarith

theorem normalizedGyiresRatio_eq_iff (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    4 * (circ w).permanent^2 / gyiresDenominator w = (24 : ℝ) / 625 ↔
      ∀ i, w i = 1 / 5 := by
  have hd := positiveDenominator w hw hsum
  have heq : (4 * (circ w).permanent^2 / gyiresDenominator w = (24 : ℝ) / 625) ↔
      24 * gyiresDenominator w = 2500 * (circ w).permanent^2 := by
    rw [div_eq_iff (ne_of_gt hd)]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact (gyires_matrix_equality_iff w hw).trans (normalized_equality_weights w hsum)

end MathAndTheory.GyiresCirculant5
