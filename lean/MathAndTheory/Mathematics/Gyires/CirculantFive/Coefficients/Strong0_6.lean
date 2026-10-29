module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a^6`

Generated certificate. The coefficient of `a^6` (a power of the smallest weight) in the chamber
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

def strong0_part_6_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 26242500) + ((d * 70170000) + (e * 34800000)))) + ((d * ((d * 89115000) + (e * 88545000))) + (e * (e * 36060000))))) + ((d * ((d * ((d * 55050000) + (e * 82290000))) + (e * (e * 62520000)))) + (e * (e * (e * 17640000)))))) + ((d * ((d * ((d * ((d * 12802500) + (e * 25605000))) + (e * (e * 27502500)))) + (e * (e * (e * 14700000))))) + (e * (e * (e * (e * 2940000))))))

private theorem strong0_part_6_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_6_0 c d e := by
  unfold strong0_part_6_0
  positivity

theorem strong0_part_6_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 6) 0 = strong0_part_6_0 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_6_0 <;> ring

def strong0_part_6_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 97005000) + ((d * 194010000) + (e * 96435000)))) + ((d * ((d * 175905000) + (e * 175335000))) + (e * (e * 78900000))))) + ((d * ((d * ((d * 58320000) + (e * 87195000))) + (e * (e * 70035000)))) + (e * (e * (e * 20580000)))))

private theorem strong0_part_6_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_6_1 c d e := by
  unfold strong0_part_6_1
  positivity

theorem strong0_part_6_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 6) 1 = strong0_part_6_1 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_6_1 <;> ring

def strong0_part_6_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * 133342500) + ((d * 177600000) + (e * 88515000)))) + ((d * ((d * 88140000) + (e * 88140000))) + (e * (e * 43882500))))

private theorem strong0_part_6_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_6_2 c d e := by
  unfold strong0_part_6_2
  positivity

theorem strong0_part_6_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 6) 2 = strong0_part_6_2 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_6_2 <;> ring

def strong0_part_6_3 (c d e : ℝ) : ℝ :=
  ((c * 89460000) + ((d * 59640000) + (e * 29820000)))

private theorem strong0_part_6_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_6_3 c d e := by
  unfold strong0_part_6_3
  positivity

theorem strong0_part_6_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 6) 3 = strong0_part_6_3 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_6_3 <;> ring

def strong0_part_6_4 (c d e : ℝ) : ℝ :=
  29820000

private theorem strong0_part_6_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_6_4 c d e := by
  unfold strong0_part_6_4
  positivity

theorem strong0_part_6_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 6) 4 = strong0_part_6_4 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_6_4 <;> ring

theorem strong0_coeff_6_length (c d e : ℝ) :
    (chamberPoly0 c d e 6).length ≤ 5 := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong0_coeff_6_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly0 c d e 6) b := by
  apply polyEval_nonneg_of_coeff _ b 5
    (strong0_coeff_6_length c d e) hb
  apply forall_fin5
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 6) 0
    rw [strong0_part_6_0_eq]
    exact strong0_part_6_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 6) 1
    rw [strong0_part_6_1_eq]
    exact strong0_part_6_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 6) 2
    rw [strong0_part_6_2_eq]
    exact strong0_part_6_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 6) 3
    rw [strong0_part_6_3_eq]
    exact strong0_part_6_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 6) 4
    rw [strong0_part_6_4_eq]
    exact strong0_part_6_4_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
