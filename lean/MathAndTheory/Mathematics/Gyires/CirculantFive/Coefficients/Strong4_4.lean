module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a^4`

Generated certificate. The coefficient of `a^4` (a power of the smallest weight) in the chamber
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

def strong4_part_4_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 22986880) + ((d * 93315820) + (e * 48710360)))) + ((d * ((d * 178360800) + (e * 186702300))) + (e * (e * 64926400))))) + ((d * ((d * ((d * 192582200) + (e * 301346400))) + (e * (e * 208908200)))) + (e * (e * (e * 52703600)))))) + ((d * ((d * ((d * ((d * 119115300) + (e * 246362100))) + (e * (e * 253685800)))) + (e * (e * (e * 127465600))))) + (e * (e * (e * (e * 24205100))))))) + ((d * ((d * ((d * ((d * ((d * 39300220) + (e * 100198000))) + (e * (e * 135848100)))) + (e * (e * (e * 102140000))))) + (e * (e * (e * (e * 39128000)))))) + (e * (e * (e * (e * (e * 5969160)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 5365780) + (e * 16097340))) + (e * (e * 26895900)))) + (e * (e * (e * 26962900))))) + (e * (e * (e * (e * 15674700)))))) + (e * (e * (e * (e * (e * 4876140))))))) + (e * (e * (e * (e * (e * (e * 630520))))))))

private theorem strong4_part_4_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_4_0 c d e := by
  unfold strong4_part_4_0
  positivity

theorem strong4_part_4_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 4) 0 = strong4_part_4_0 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_4_0 <;> ring

def strong4_part_4_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 146489940) + ((d * 493483000) + (e * 254911400)))) + ((d * ((d * 769076100) + (e * 795730800))) + (e * (e * 284934800))))) + ((d * ((d * ((d * 641708400) + (e * 989007300))) + (e * (e * 696736200)))) + (e * (e * (e * 180389400)))))) + ((d * ((d * ((d * ((d * 273093300) + (e * 554659800))) + (e * (e * 573354100)))) + (e * (e * (e * 292814200))))) + (e * (e * (e * (e * 56449100))))))) + ((d * ((d * ((d * ((d * ((d * 46405760) + (e * 116014400))) + (e * (e * 156322800)))) + (e * (e * (e * 118469800))))) + (e * (e * (e * (e * 45880000)))))) + (e * (e * (e * (e * (e * 7062180)))))))

private theorem strong4_part_4_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_4_1 c d e := by
  unfold strong4_part_4_1
  positivity

theorem strong4_part_4_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 4) 1 = strong4_part_4_1 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_4_1 <;> ring

def strong4_part_4_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 384603900) + ((d * 1033634100) + (e * 527512800)))) + ((d * ((d * 1238587300) + (e * 1266057100))) + (e * (e * 469593100))))) + ((d * ((d * ((d * 713640200) + (e * 1084195200))) + (e * (e * 777781900)))) + (e * (e * (e * 206652600)))))) + ((d * ((d * ((d * ((d * 157078900) + (e * 314157800))) + (e * (e * 326160100)))) + (e * (e * (e * 169081200))))) + (e * (e * (e * (e * 32995800))))))

private theorem strong4_part_4_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_4_2 c d e := by
  unfold strong4_part_4_2
  positivity

theorem strong4_part_4_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 4) 2 = strong4_part_4_2 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_4_2 <;> ring

def strong4_part_4_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 538663900) + ((d * 1083641000) + (e * 546398800)))) + ((d * ((d * 890680600) + (e * 899837200))) + (e * (e * 347125200))))) + ((d * ((d * ((d * 266321600) + (e * 399482400))) + (e * (e * 291924600)))) + (e * (e * (e * 79381900)))))

private theorem strong4_part_4_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_4_3 c d e := by
  unfold strong4_part_4_3
  positivity

theorem strong4_part_4_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 4) 3 = strong4_part_4_3 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_4_3 <;> ring

def strong4_part_4_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * 435607200) + ((d * 582914000) + (e * 291457000)))) + ((d * ((d * 245599100) + (e * 245599100))) + (e * (e * 98292300))))

private theorem strong4_part_4_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_4_4 c d e := by
  unfold strong4_part_4_4
  positivity

theorem strong4_part_4_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 4) 4 = strong4_part_4_4 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_4_4 <;> ring

def strong4_part_4_5 (c d e : ℝ) : ℝ :=
  ((c * 202388940) + ((d * 134925960) + (e * 67462980)))

private theorem strong4_part_4_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_4_5 c d e := by
  unfold strong4_part_4_5
  positivity

theorem strong4_part_4_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 4) 5 = strong4_part_4_5 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_4_5 <;> ring

def strong4_part_4_6 (c d e : ℝ) : ℝ :=
  44975320

private theorem strong4_part_4_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_4_6 c d e := by
  unfold strong4_part_4_6
  positivity

theorem strong4_part_4_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 4) 6 = strong4_part_4_6 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_4_6 <;> ring

theorem strong4_coeff_4_length (c d e : ℝ) :
    (chamberPoly4 c d e 4).length ≤ 7 := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong4_coeff_4_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly4 c d e 4) b := by
  apply polyEval_nonneg_of_coeff _ b 7
    (strong4_coeff_4_length c d e) hb
  apply forall_fin7
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 4) 0
    rw [strong4_part_4_0_eq]
    exact strong4_part_4_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 4) 1
    rw [strong4_part_4_1_eq]
    exact strong4_part_4_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 4) 2
    rw [strong4_part_4_2_eq]
    exact strong4_part_4_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 4) 3
    rw [strong4_part_4_3_eq]
    exact strong4_part_4_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 4) 4
    rw [strong4_part_4_4_eq]
    exact strong4_part_4_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 4) 5
    rw [strong4_part_4_5_eq]
    exact strong4_part_4_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 4) 6
    rw [strong4_part_4_6_eq]
    exact strong4_part_4_6_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
