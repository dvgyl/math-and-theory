module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a⁰ b^9`

Generated certificate. The coefficient of `b^9` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly5` is an explicit polynomial in `c`, `d`, `e` with
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

def strong5_part_0_9 (c d e : ℝ) : ℝ :=
  ((c * 1749720) + ((d * 1166480) + (e * 583240)))

private theorem strong5_part_0_9_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_0_9 c d e := by
  unfold strong5_part_0_9
  positivity

theorem strong5_part_0_9_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 0) 9 = strong5_part_0_9 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift5_0_eq, compactShift5_1_eq, compactShift5_2_eq,
    compactShift5_3_eq, compactShift5_4_eq, compactShift5_5_eq,
    compactGram5_0_eq, compactGram5_1_eq, compactGram5_2_eq]
  dsimp only [compactShift5_0, compactShift5_1, compactShift5_2,
    compactShift5_3, compactShift5_4, compactShift5_5,
    compactGram5_0, compactGram5_1, compactGram5_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly5, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong5_part_0_9 <;> ring

theorem strong5_part_0_9_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly5 c d e 0) 9 := by
  rw [strong5_part_0_9_eq]
  exact strong5_part_0_9_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
