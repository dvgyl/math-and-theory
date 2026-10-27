module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a^7`

Generated certificate. The coefficient of `a^7` (a power of the smallest weight) in the chamber
polynomial `chamberPoly0` is a polynomial in the first gap `b` whose coefficients are explicit
polynomials in `c`, `d`, `e` with nonnegative integer coefficients. Each is proved equal to the
computed coefficient by `ring` and nonnegative by `positivity`, so the whole coefficient is
nonnegative for `b, c, d, e ≥ 0`.
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

def strong0_part_7_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 12720000) + ((d * 25440000) + (e * 12720000)))) + ((d * ((d * 24960000) + (e * 24960000))) + (e * (e * 12240000))))) + ((d * ((d * ((d * 8880000) + (e * 13320000))) + (e * (e * 11160000)))) + (e * (e * (e * 3360000)))))

private theorem strong0_part_7_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_7_0 c d e := by
  unfold strong0_part_7_0
  positivity

theorem strong0_part_7_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 7) 0 = strong0_part_7_0 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_7_0 <;> ring

def strong0_part_7_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * 29880000) + ((d * 39840000) + (e * 19920000)))) + ((d * ((d * 23280000) + (e * 23280000))) + (e * (e * 13320000))))

private theorem strong0_part_7_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_7_1 c d e := by
  unfold strong0_part_7_1
  positivity

theorem strong0_part_7_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 7) 1 = strong0_part_7_1 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_7_1 <;> ring

def strong0_part_7_2 (c d e : ℝ) : ℝ :=
  ((c * 24840000) + ((d * 16560000) + (e * 8280000)))

private theorem strong0_part_7_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_7_2 c d e := by
  unfold strong0_part_7_2
  positivity

theorem strong0_part_7_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 7) 2 = strong0_part_7_2 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_7_2 <;> ring

def strong0_part_7_3 (c d e : ℝ) : ℝ :=
  11040000

private theorem strong0_part_7_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_7_3 c d e := by
  unfold strong0_part_7_3
  positivity

theorem strong0_part_7_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 7) 3 = strong0_part_7_3 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_7_3 <;> ring

theorem strong0_coeff_7_length (c d e : ℝ) :
    (chamberPoly0 c d e 7).length ≤ 4 := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num

theorem strong0_coeff_7_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly0 c d e 7) b := by
  apply polyEval_nonneg_of_coeff _ b 4
    (strong0_coeff_7_length c d e) hb
  apply forall_fin4
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 7) 0
    rw [strong0_part_7_0_eq]
    exact strong0_part_7_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 7) 1
    rw [strong0_part_7_1_eq]
    exact strong0_part_7_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 7) 2
    rw [strong0_part_7_2_eq]
    exact strong0_part_7_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 7) 3
    rw [strong0_part_7_3_eq]
    exact strong0_part_7_3_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
