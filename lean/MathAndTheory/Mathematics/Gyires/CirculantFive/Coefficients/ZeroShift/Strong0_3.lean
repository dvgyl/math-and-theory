module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a⁰ b^3`

Generated certificate. The coefficient of `b^3` in the constant term (in the smallest weight
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

def strong0_part_0_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 7923830) + ((d * 39574110) + (e * 17905740)))) + ((d * ((d * 89930750) + (e * 79786160))) + (e * (e * 22885920))))) + ((d * ((d * ((d * 115345390) + (e * 150469540))) + (e * (e * 87292280)))) + (e * (e * (e * 21013850)))))) + ((d * ((d * ((d * ((d * 88310920) + (e * 151029160))) + (e * (e * 133155130)))) + (e * (e * (e * 65553420))))) + (e * (e * (e * (e * 13296080))))))) + ((d * ((d * ((d * ((d * ((d * 39922360) + (e * 84257310))) + (e * (e * 101002040)))) + (e * (e * (e * 76274110))))) + (e * (e * (e * (e * 31454120)))))) + (e * (e * (e * (e * (e * 5323990)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 9807380) + (e * 24698720))) + (e * (e * 38166900)))) + (e * (e * (e * 39404560))))) + (e * (e * (e * (e * 24690760)))))) + (e * (e * (e * (e * (e * 8440600))))))) + (e * (e * (e * (e * (e * (e * 1221730))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1006480) + (e * 2979860))) + (e * (e * 5787160)))) + (e * (e * (e * 7676470))))) + (e * (e * (e * (e * 6473850)))))) + (e * (e * (e * (e * (e * 3332270))))))) + (e * (e * (e * (e * (e * (e * 970190)))))))) + (e * (e * (e * (e * (e * (e * (e * 124540)))))))))

private theorem strong0_part_0_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_0_3 c d e := by
  unfold strong0_part_0_3
  positivity

theorem strong0_part_0_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 0) 3 = strong0_part_0_3 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong0_part_0_3 <;> ring

theorem strong0_part_0_3_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly0 c d e 0) 3 := by
  rw [strong0_part_0_3_eq]
  exact strong0_part_0_3_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
