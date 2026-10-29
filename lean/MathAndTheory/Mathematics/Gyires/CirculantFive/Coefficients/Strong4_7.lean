module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a^7`

Generated certificate. The coefficient of `a^7` (a power of the smallest weight) in the chamber
polynomial `chamberPoly4` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong4_part_7_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 12720000) + ((d * 25440000) + (e * 12720000)))) + ((d * ((d * 24960000) + (e * 24960000))) + (e * (e * 12240000))))) + ((d * ((d * ((d * 8880000) + (e * 13320000))) + (e * (e * 11160000)))) + (e * (e * (e * 3360000)))))

private theorem strong4_part_7_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_7_0 c d e := by
  unfold strong4_part_7_0
  positivity

theorem strong4_part_7_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 7) 0 = strong4_part_7_0 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_7_0 <;> ring

def strong4_part_7_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * 29880000) + ((d * 39840000) + (e * 19920000)))) + ((d * ((d * 23280000) + (e * 23280000))) + (e * (e * 13320000))))

private theorem strong4_part_7_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_7_1 c d e := by
  unfold strong4_part_7_1
  positivity

theorem strong4_part_7_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 7) 1 = strong4_part_7_1 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_7_1 <;> ring

def strong4_part_7_2 (c d e : ℝ) : ℝ :=
  ((c * 24840000) + ((d * 16560000) + (e * 8280000)))

private theorem strong4_part_7_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_7_2 c d e := by
  unfold strong4_part_7_2
  positivity

theorem strong4_part_7_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 7) 2 = strong4_part_7_2 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_7_2 <;> ring

def strong4_part_7_3 (c d e : ℝ) : ℝ :=
  11040000

private theorem strong4_part_7_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_7_3 c d e := by
  unfold strong4_part_7_3
  positivity

theorem strong4_part_7_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 7) 3 = strong4_part_7_3 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_7_3 <;> ring

theorem strong4_coeff_7_length (c d e : ℝ) :
    (chamberPoly4 c d e 7).length ≤ 4 := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (7 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart7, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num

theorem strong4_coeff_7_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly4 c d e 7) b := by
  apply polyEval_nonneg_of_coeff _ b 4
    (strong4_coeff_7_length c d e) hb
  apply forall_fin4
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 7) 0
    rw [strong4_part_7_0_eq]
    exact strong4_part_7_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 7) 1
    rw [strong4_part_7_1_eq]
    exact strong4_part_7_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 7) 2
    rw [strong4_part_7_2_eq]
    exact strong4_part_7_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 7) 3
    rw [strong4_part_7_3_eq]
    exact strong4_part_7_3_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
