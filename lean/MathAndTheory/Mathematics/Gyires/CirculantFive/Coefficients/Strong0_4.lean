module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a^4`

Generated certificate. The coefficient of `a^4` (a power of the smallest weight) in the chamber
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

def strong0_part_4_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 22986880) + ((d * 93315820) + (e * 44605460)))) + ((d * ((d * 178360800) + (e * 170019300))) + (e * (e * 56584900))))) + ((d * ((d * ((d * 192582200) + (e * 276400200))) + (e * (e * 183962000)))) + (e * (e * (e * 47440400)))))) + ((d * ((d * ((d * ((d * 119115300) + (e * 230099100))) + (e * (e * 229291300)))) + (e * (e * (e * 117280900))))) + (e * (e * (e * (e * 23178500))))))) + ((d * ((d * ((d * ((d * ((d * 39300220) + (e * 96303100))) + (e * (e * 128058300)))) + (e * (e * (e * 97218500))))) + (e * (e * (e * (e * 38101400)))))) + (e * (e * (e * (e * (e * 5969160)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 5365780) + (e * 16097340))) + (e * (e * 26895900)))) + (e * (e * (e * 26962900))))) + (e * (e * (e * (e * 15674700)))))) + (e * (e * (e * (e * (e * 4876140))))))) + (e * (e * (e * (e * (e * (e * 630520))))))))

private theorem strong0_part_4_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_4_0 c d e := by
  unfold strong0_part_4_0
  positivity

theorem strong0_part_4_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 4) 0 = strong0_part_4_0 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_4_0 <;> ring

def strong0_part_4_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 146489940) + ((d * 493878100) + (e * 238966700)))) + ((d * ((d * 768893100) + (e * 744001800))) + (e * (e * 260043500))))) + ((d * ((d * ((d * 639262200) + (e * 929198700))) + (e * (e * 639847200)))) + (e * (e * (e * 169521300)))))) + ((d * ((d * ((d * ((d * 270330300) + (e * 526450800))) + (e * (e * 534645100)))) + (e * (e * (e * 277498000))))) + (e * (e * (e * (e * 55422500))))))) + ((d * ((d * ((d * ((d * ((d * 45510860) + (e * 111829700))) + (e * (e * 149611500)))) + (e * (e * (e * 114021700))))) + (e * (e * (e * (e * 44853400)))))) + (e * (e * (e * (e * (e * 7062180)))))))

private theorem strong0_part_4_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_4_1 c d e := by
  unfold strong0_part_4_1
  positivity

theorem strong0_part_4_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 4) 1 = strong0_part_4_1 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_4_1 <;> ring

def strong0_part_4_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 384603900) + ((d * 1032294300) + (e * 504781500)))) + ((d * ((d * 1231382800) + (e * 1207098100))) + (e * (e * 445308400))))) + ((d * ((d * ((d * 703724000) + (e * 1033786200))) + (e * (e * 737762500)))) + (e * (e * (e * 201047700)))))) + ((d * ((d * ((d * ((d * 153027400) + (e * 299976500))) + (e * (e * 310425400)))) + (e * (e * (e * 163476300))))) + (e * (e * (e * (e * 32995800))))))

private theorem strong0_part_4_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_4_2 c d e := by
  unfold strong0_part_4_2
  positivity

theorem strong0_part_4_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 4) 2 = strong0_part_4_2 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_4_2 <;> ring

def strong0_part_4_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 538663900) + ((d * 1078749500) + (e * 532350700)))) + ((d * ((d * 879475900) + (e * 871741000))) + (e * (e * 339390300))))) + ((d * ((d * ((d * 260008400) + (e * 385434300))) + (e * (e * 284189700)))) + (e * (e * (e * 79381900)))))

private theorem strong0_part_4_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_4_3 c d e := by
  unfold strong0_part_4_3
  positivity

theorem strong0_part_4_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 4) 3 = strong0_part_4_3 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_4_3 <;> ring

def strong0_part_4_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * 435607200) + ((d * 579757400) + (e * 288300400)))) + ((d * ((d * 242442500) + (e * 242442500))) + (e * (e * 98292300))))

private theorem strong0_part_4_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_4_4 c d e := by
  unfold strong0_part_4_4
  positivity

theorem strong0_part_4_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 4) 4 = strong0_part_4_4 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_4_4 <;> ring

def strong0_part_4_5 (c d e : ℝ) : ℝ :=
  ((c * 202388940) + ((d * 134925960) + (e * 67462980)))

private theorem strong0_part_4_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_4_5 c d e := by
  unfold strong0_part_4_5
  positivity

theorem strong0_part_4_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 4) 5 = strong0_part_4_5 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_4_5 <;> ring

def strong0_part_4_6 (c d e : ℝ) : ℝ :=
  44975320

private theorem strong0_part_4_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_4_6 c d e := by
  unfold strong0_part_4_6
  positivity

theorem strong0_part_4_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 4) 6 = strong0_part_4_6 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_4_6 <;> ring

theorem strong0_coeff_4_length (c d e : ℝ) :
    (chamberPoly0 c d e 4).length ≤ 7 := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong0_coeff_4_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly0 c d e 4) b := by
  apply polyEval_nonneg_of_coeff _ b 7
    (strong0_coeff_4_length c d e) hb
  apply forall_fin7
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 4) 0
    rw [strong0_part_4_0_eq]
    exact strong0_part_4_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 4) 1
    rw [strong0_part_4_1_eq]
    exact strong0_part_4_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 4) 2
    rw [strong0_part_4_2_eq]
    exact strong0_part_4_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 4) 3
    rw [strong0_part_4_3_eq]
    exact strong0_part_4_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 4) 4
    rw [strong0_part_4_4_eq]
    exact strong0_part_4_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 4) 5
    rw [strong0_part_4_5_eq]
    exact strong0_part_4_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 4) 6
    rw [strong0_part_4_6_eq]
    exact strong0_part_4_6_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
