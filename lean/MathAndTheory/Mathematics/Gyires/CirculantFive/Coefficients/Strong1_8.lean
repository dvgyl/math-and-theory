module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a^8`

Generated certificate. The coefficient of `a^8` (a power of the smallest weight) in the chamber
polynomial `chamberPoly1` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong1_part_8_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * 2700000) + ((d * 3600000) + (e * 1800000)))) + ((d * ((d * 2700000) + (e * 2700000))) + (e * (e * 1800000))))

private theorem strong1_part_8_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_8_0 c d e := by
  unfold strong1_part_8_0
  positivity

theorem strong1_part_8_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 8) 0 = strong1_part_8_0 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_8_0 <;> ring

def strong1_part_8_1 (c d e : ℝ) : ℝ :=
  ((c * 2700000) + ((d * 1800000) + (e * 900000)))

private theorem strong1_part_8_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_8_1 c d e := by
  unfold strong1_part_8_1
  positivity

theorem strong1_part_8_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 8) 1 = strong1_part_8_1 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_8_1 <;> ring

def strong1_part_8_2 (c d e : ℝ) : ℝ :=
  1800000

private theorem strong1_part_8_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_8_2 c d e := by
  unfold strong1_part_8_2
  positivity

theorem strong1_part_8_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 8) 2 = strong1_part_8_2 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_8_2 <;> ring

theorem strong1_coeff_8_length (c d e : ℝ) :
    (chamberPoly1 c d e 8).length ≤ 3 := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num

theorem strong1_coeff_8_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly1 c d e 8) b := by
  apply polyEval_nonneg_of_coeff _ b 3
    (strong1_coeff_8_length c d e) hb
  apply forall_fin3
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 8) 0
    rw [strong1_part_8_0_eq]
    exact strong1_part_8_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 8) 1
    rw [strong1_part_8_1_eq]
    exact strong1_part_8_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 8) 2
    rw [strong1_part_8_2_eq]
    exact strong1_part_8_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
