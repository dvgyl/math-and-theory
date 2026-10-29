module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a⁰ b^6`

Generated certificate. The coefficient of `b^6` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly2` is an explicit polynomial in `c`, `d`, `e` with
nonnegative integer coefficients; it is proved equal to the computed coefficient by `ring` and
nonnegative for `c, d, e ≥ 0` by `positivity`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace MathAndTheory.GyiresCirculant5

def strong2_part_0_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 20858825) + ((d * 54485550) + (e * 28180420)))) + ((d * ((d * 60220460) + (e * 62183900))) + (e * (e * 20339320))))) + ((d * ((d * ((d * 32064820) + (e * 50210720))) + (e * (e * 33445750)))) + (e * (e * (e * 7841360)))))) + ((d * ((d * ((d * ((d * 6685320) + (e * 14266900))) + (e * (e * 14378860)))) + (e * (e * (e * 6797280))))) + (e * (e * (e * (e * 1214235))))))

private theorem strong2_part_0_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_0_6 c d e := by
  unfold strong2_part_0_6
  positivity

theorem strong2_part_0_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 0) 6 = strong2_part_0_6 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift2_0_eq, compactShift2_1_eq, compactShift2_2_eq,
    compactShift2_3_eq, compactShift2_4_eq, compactShift2_5_eq,
    compactGram2_0_eq, compactGram2_1_eq, compactGram2_2_eq]
  dsimp only [compactShift2_0, compactShift2_1, compactShift2_2,
    compactShift2_3, compactShift2_4, compactShift2_5,
    compactGram2_0, compactGram2_1, compactGram2_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly2, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong2_part_0_6 <;> ring

theorem strong2_part_0_6_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly2 c d e 0) 6 := by
  rw [strong2_part_0_6_eq]
  exact strong2_part_0_6_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
