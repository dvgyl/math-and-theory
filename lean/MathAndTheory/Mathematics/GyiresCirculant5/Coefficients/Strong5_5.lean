module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a^5`

Generated certificate. The coefficient of `a^5` (a power of the smallest weight) in the chamber
polynomial `chamberPoly5` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong5_part_5_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 31011720) + ((d * 104156400) + (e * 50902200)))) + ((d * ((d * 164905200) + (e * 161269200))) + (e * (e * 58396800))))) + ((d * ((d * ((d * 140644800) + (e * 207223200))) + (e * (e * 146361600)))) + (e * (e * (e * 39249600)))))) + ((d * ((d * ((d * ((d * 61038600) + (e * 120793200))) + (e * (e * 124799400)))) + (e * (e * (e * 65044800))))) + (e * (e * (e * (e * 12897600))))))) + ((d * ((d * ((d * ((d * ((d * 10523280) + (e * 26308200))) + (e * (e * 35575200)))) + (e * (e * (e * 27054600))))) + (e * (e * (e * (e * 10526400)))))) + (e * (e * (e * (e * (e * 1631040)))))))

private theorem strong5_part_5_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_5_0 c d e := by
  unfold strong5_part_5_0
  positivity

theorem strong5_part_5_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 5) 0 = strong5_part_5_0 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_5_0 <;> ring

def strong5_part_5_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 156256800) + ((d * 419248800) + (e * 206630400)))) + ((d * ((d * 516088800) + (e * 508816800))) + (e * (e * 195667200))))) + ((d * ((d * ((d * 307288800) + (e * 457297200))) + (e * (e * 335631600)))) + (e * (e * (e * 92169600)))))) + ((d * ((d * ((d * ((d * 69460800) + (e * 138921600))) + (e * (e * 146725200)))) + (e * (e * (e * 77264400))))) + (e * (e * (e * (e * 15268800))))))

private theorem strong5_part_5_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_5_1 c d e := by
  unfold strong5_part_5_1
  positivity

theorem strong5_part_5_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 5) 1 = strong5_part_5_1 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_5_1 <;> ring

def strong5_part_5_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 310789800) + ((d * 624783600) + (e * 310573800)))) + ((d * ((d * 536540400) + (e * 532904400))) + (e * (e * 219126600))))) + ((d * ((d * ((d * 168367200) + (e * 252550800))) + (e * (e * 192542400)))) + (e * (e * (e * 54179400)))))

private theorem strong5_part_5_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_5_2 c d e := by
  unfold strong5_part_5_2
  positivity

theorem strong5_part_5_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 5) 2 = strong5_part_5_2 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_5_2 <;> ring

def strong5_part_5_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * 314360400) + ((d * 420571200) + (e * 210285600)))) + ((d * ((d * 189326400) + (e * 189326400))) + (e * (e * 83115600))))

private theorem strong5_part_5_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_5_3 c d e := by
  unfold strong5_part_5_3
  positivity

theorem strong5_part_5_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 5) 3 = strong5_part_5_3 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_5_3 <;> ring

def strong5_part_5_4 (c d e : ℝ) : ℝ :=
  ((c * 173433600) + ((d * 115622400) + (e * 57811200)))

private theorem strong5_part_5_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_5_4 c d e := by
  unfold strong5_part_5_4
  positivity

theorem strong5_part_5_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 5) 4 = strong5_part_5_4 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_5_4 <;> ring

def strong5_part_5_5 (c d e : ℝ) : ℝ :=
  46248960

private theorem strong5_part_5_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_5_5 c d e := by
  unfold strong5_part_5_5
  positivity

theorem strong5_part_5_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 5) 5 = strong5_part_5_5 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_5_5 <;> ring

theorem strong5_coeff_5_length (c d e : ℝ) :
    (chamberPoly5 c d e 5).length ≤ 6 := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num

theorem strong5_coeff_5_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly5 c d e 5) b := by
  apply polyEval_nonneg_of_coeff _ b 6
    (strong5_coeff_5_length c d e) hb
  apply forall_fin6
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 5) 0
    rw [strong5_part_5_0_eq]
    exact strong5_part_5_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 5) 1
    rw [strong5_part_5_1_eq]
    exact strong5_part_5_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 5) 2
    rw [strong5_part_5_2_eq]
    exact strong5_part_5_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 5) 3
    rw [strong5_part_5_3_eq]
    exact strong5_part_5_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 5) 4
    rw [strong5_part_5_4_eq]
    exact strong5_part_5_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 5) 5
    rw [strong5_part_5_5_eq]
    exact strong5_part_5_5_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
