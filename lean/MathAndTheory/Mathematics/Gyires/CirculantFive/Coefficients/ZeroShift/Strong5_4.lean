module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a⁰ b^4`

Generated certificate. The coefficient of `b^4` in the constant term (in the smallest weight
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

def strong5_part_0_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 15805330) + ((d * 63472320) + (e * 27947830)))) + ((d * ((d * 115382690) + (e * 99759620))) + (e * (e * 29321175))))) + ((d * ((d * ((d * 116602930) + (e * 153080600))) + (e * (e * 93554800)))) + (e * (e * (e * 23030140)))))) + ((d * ((d * ((d * ((d * 67560315) + (e * 122054230))) + (e * (e * 116879535)))) + (e * (e * (e * 59020690))))) + (e * (e * (e * (e * 11536570))))))) + ((d * ((d * ((d * ((d * ((d * 21068020) + (e * 49789950))) + (e * (e * 66437430)))) + (e * (e * (e * 51236690))))) + (e * (e * (e * (e * 20211860)))))) + (e * (e * (e * (e * (e * 3148090)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 2755260) + (e * 8265780))) + (e * (e * 14399915)))) + (e * (e * (e * 15023530))))) + (e * (e * (e * (e * 8937965)))))) + (e * (e * (e * (e * (e * 2803830))))))) + (e * (e * (e * (e * (e * (e * 360325))))))))

private theorem strong5_part_0_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_0_4 c d e := by
  unfold strong5_part_0_4
  positivity

theorem strong5_part_0_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 0) 4 = strong5_part_0_4 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong5_part_0_4 <;> ring

theorem strong5_part_0_4_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly5 c d e 0) 4 := by
  rw [strong5_part_0_4_eq]
  exact strong5_part_0_4_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
