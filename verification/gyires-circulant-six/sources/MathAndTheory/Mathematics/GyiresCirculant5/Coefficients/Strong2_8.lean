module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a^8`

Generated certificate. The coefficient of `a^8` (a power of the smallest weight) in the chamber
polynomial `chamberPoly2` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong2_part_8_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * 2700000) + ((d * 3600000) + (e * 1800000)))) + ((d * ((d * 2700000) + (e * 2700000))) + (e * (e * 1800000))))

private theorem strong2_part_8_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_8_0 c d e := by
  unfold strong2_part_8_0
  positivity

theorem strong2_part_8_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 8) 0 = strong2_part_8_0 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_8_0 <;> ring

def strong2_part_8_1 (c d e : ℝ) : ℝ :=
  ((c * 2700000) + ((d * 1800000) + (e * 900000)))

private theorem strong2_part_8_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_8_1 c d e := by
  unfold strong2_part_8_1
  positivity

theorem strong2_part_8_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 8) 1 = strong2_part_8_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_8_1 <;> ring

def strong2_part_8_2 (c d e : ℝ) : ℝ :=
  1800000

private theorem strong2_part_8_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_8_2 c d e := by
  unfold strong2_part_8_2
  positivity

theorem strong2_part_8_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 8) 2 = strong2_part_8_2 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_8_2 <;> ring

theorem strong2_coeff_8_length (c d e : ℝ) :
    (chamberPoly2 c d e 8).length ≤ 3 := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (8 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart8, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num

theorem strong2_coeff_8_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly2 c d e 8) b := by
  apply polyEval_nonneg_of_coeff _ b 3
    (strong2_coeff_8_length c d e) hb
  apply forall_fin3
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 8) 0
    rw [strong2_part_8_0_eq]
    exact strong2_part_8_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 8) 1
    rw [strong2_part_8_1_eq]
    exact strong2_part_8_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 8) 2
    rw [strong2_part_8_2_eq]
    exact strong2_part_8_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
