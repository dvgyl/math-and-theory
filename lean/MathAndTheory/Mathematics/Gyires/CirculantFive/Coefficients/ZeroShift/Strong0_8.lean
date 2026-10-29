module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a⁰ b^8`

Generated certificate. The coefficient of `b^8` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly0` is an explicit polynomial in `c`, `d`, `e` with
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

def strong0_part_0_8 (c d e : ℝ) : ℝ :=
  ((c * ((c * 6286425) + ((d * 8396620) + (e * 4220390)))) + ((d * ((d * 3147460) + (e * 3147460))) + (e * (e * 1037265))))

private theorem strong0_part_0_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_0_8 c d e := by
  unfold strong0_part_0_8
  positivity

theorem strong0_part_0_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 0) 8 = strong0_part_0_8 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_0_8 <;> ring

theorem strong0_part_0_8_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly0 c d e 0) 8 := by
  rw [strong0_part_0_8_eq]
  exact strong0_part_0_8_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
