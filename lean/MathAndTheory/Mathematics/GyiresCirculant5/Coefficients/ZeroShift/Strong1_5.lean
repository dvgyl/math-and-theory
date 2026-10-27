module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a⁰ b^5`

Generated certificate. The coefficient of `b^5` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly1` is an explicit polynomial in `c`, `d`, `e` with
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

def strong1_part_0_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 21700744) + ((d * 75451830) + (e * 39039100)))) + ((d * ((d * 114114060) + (e * 119605880))) + (e * (e * 39451410))))) + ((d * ((d * ((d * 89011450) + (e * 142653780))) + (e * (e * 95569860)))) + (e * (e * (e * 22519340)))))) + ((d * ((d * ((d * ((d * 34812660) + (e * 75683380))) + (e * (e * 76996620)))) + (e * (e * (e * 36637520))))) + (e * (e * (e * (e * 6570470))))))) + ((d * ((d * ((d * ((d * ((d * 5386816) + (e * 14822940))) + (e * (e * 20321650)))) + (e * (e * (e * 14674700))))) + (e * (e * (e * (e * 5343910)))))) + (e * (e * (e * (e * (e * 777368)))))))

private theorem strong1_part_0_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_0_5 c d e := by
  unfold strong1_part_0_5
  positivity

theorem strong1_part_0_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 0) 5 = strong1_part_0_5 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_0_5 <;> ring

theorem strong1_part_0_5_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly1 c d e 0) 5 := by
  rw [strong1_part_0_5_eq]
  exact strong1_part_0_5_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
