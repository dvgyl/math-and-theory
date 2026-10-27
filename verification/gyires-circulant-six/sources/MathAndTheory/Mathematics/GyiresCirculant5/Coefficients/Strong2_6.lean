module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a^6`

Generated certificate. The coefficient of `a^6` (a power of the smallest weight) in the chamber
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

def strong2_part_6_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 26242500) + ((d * 69600000) + (e * 34800000)))) + ((d * ((d * 87975000) + (e * 87975000))) + (e * (e * 36060000))))) + ((d * ((d * ((d * 54480000) + (e * 81720000))) + (e * (e * 62520000)))) + (e * (e * (e * 17640000)))))) + ((d * ((d * ((d * ((d * 12802500) + (e * 25605000))) + (e * (e * 27502500)))) + (e * (e * (e * 14700000))))) + (e * (e * (e * (e * 2940000))))))

private theorem strong2_part_6_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_6_0 c d e := by
  unfold strong2_part_6_0
  positivity

theorem strong2_part_6_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 6) 0 = strong2_part_6_0 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_6_0 <;> ring

def strong2_part_6_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 97005000) + ((d * 193440000) + (e * 96435000)))) + ((d * ((d * 175335000) + (e * 175335000))) + (e * (e * 78900000))))) + ((d * ((d * ((d * 58320000) + (e * 87765000))) + (e * (e * 70605000)))) + (e * (e * (e * 20580000)))))

private theorem strong2_part_6_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_6_1 c d e := by
  unfold strong2_part_6_1
  positivity

theorem strong2_part_6_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 6) 1 = strong2_part_6_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_6_1 <;> ring

def strong2_part_6_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * 133342500) + ((d * 177600000) + (e * 88515000)))) + ((d * ((d * 88140000) + (e * 88140000))) + (e * (e * 43882500))))

private theorem strong2_part_6_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_6_2 c d e := by
  unfold strong2_part_6_2
  positivity

theorem strong2_part_6_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 6) 2 = strong2_part_6_2 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_6_2 <;> ring

def strong2_part_6_3 (c d e : ℝ) : ℝ :=
  ((c * 89460000) + ((d * 59640000) + (e * 29820000)))

private theorem strong2_part_6_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_6_3 c d e := by
  unfold strong2_part_6_3
  positivity

theorem strong2_part_6_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 6) 3 = strong2_part_6_3 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_6_3 <;> ring

def strong2_part_6_4 (c d e : ℝ) : ℝ :=
  29820000

private theorem strong2_part_6_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_6_4 c d e := by
  unfold strong2_part_6_4
  positivity

theorem strong2_part_6_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 6) 4 = strong2_part_6_4 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_6_4 <;> ring

theorem strong2_coeff_6_length (c d e : ℝ) :
    (chamberPoly2 c d e 6).length ≤ 5 := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (6 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart6, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong2_coeff_6_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly2 c d e 6) b := by
  apply polyEval_nonneg_of_coeff _ b 5
    (strong2_coeff_6_length c d e) hb
  apply forall_fin5
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 6) 0
    rw [strong2_part_6_0_eq]
    exact strong2_part_6_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 6) 1
    rw [strong2_part_6_1_eq]
    exact strong2_part_6_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 6) 2
    rw [strong2_part_6_2_eq]
    exact strong2_part_6_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 6) 3
    rw [strong2_part_6_3_eq]
    exact strong2_part_6_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 6) 4
    rw [strong2_part_6_4_eq]
    exact strong2_part_6_4_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
