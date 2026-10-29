module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a^2`

Generated certificate. The coefficient of `a^2` (a power of the smallest weight) in the chamber
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

def strong4_part_2_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 3298205) + ((d * 18285710) + (e * 10185780)))) + ((d * ((d * 47604275) + (e * 53685400))) + (e * (e * 18035170))))) + ((d * ((d * ((d * 72750900) + (e * 123507010))) + (e * (e * 84780270)))) + (e * (e * (e * 20449840)))))) + ((d * ((d * ((d * ((d * 69859825) + (e * 157527250))) + (e * (e * 164784750)))) + (e * (e * (e * 81022150))))) + (e * (e * (e * (e * 14948775))))))) + ((d * ((d * ((d * ((d * ((d * 42723780) + (e * 119067230))) + (e * (e * 168242930)))) + (e * (e * (e * 126559420))))) + (e * (e * (e * (e * 47820950)))))) + (e * (e * (e * (e * (e * 7169360)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 16182515) + (e * 53014870))) + (e * (e * 94722795)))) + (e * (e * (e * 97099170))))) + (e * (e * (e * (e * 56494270)))))) + (e * (e * (e * (e * (e * 17438670))))))) + (e * (e * (e * (e * (e * (e * 2228210))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3469070) + (e * 12816430))) + (e * (e * 27755640)))) + (e * (e * (e * 36470430))))) + (e * (e * (e * (e * 29159820)))))) + (e * (e * (e * (e * (e * 13956990))))))) + (e * (e * (e * (e * (e * (e * 3700800)))))))) + (e * (e * (e * (e * (e * (e * (e * 420740)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 322745) + (e * 1290980))) + (e * (e * 3285340)))) + (e * (e * (e * 5337590))))) + (e * (e * (e * (e * 5528370)))))) + (e * (e * (e * (e * (e * 3666900))))))) + (e * (e * (e * (e * (e * (e * 1521805)))))))) + (e * (e * (e * (e * (e * (e * (e * 362790))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 38105))))))))))

private theorem strong4_part_2_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_0 c d e := by
  unfold strong4_part_2_0
  positivity

theorem strong4_part_2_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 0 = strong4_part_2_0 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_0 <;> ring

def strong4_part_2_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 29641340) + ((d * 141931150) + (e * 77912070)))) + ((d * ((d * 317026750) + (e * 351364580))) + (e * (e * 118973670))))) + ((d * ((d * ((d * 408463430) + (e * 677471550))) + (e * (e * 465896310)))) + (e * (e * (e * 114000400)))))) + ((d * ((d * ((d * ((d * 319755730) + (e * 699207460))) + (e * (e * 727196430)))) + (e * (e * (e * 360792660))))) + (e * (e * (e * (e * 67315950))))))) + ((d * ((d * ((d * ((d * ((d * 150349570) + (e * 402994830))) + (e * (e * 560967650)))) + (e * (e * (e * 423351720))))) + (e * (e * (e * (e * 161179770)))))) + (e * (e * (e * (e * (e * 24341880)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 39155200) + (e * 122352140))) + (e * (e * 213003890)))) + (e * (e * (e * 217621320))))) + (e * (e * (e * (e * 127082920)))))) + (e * (e * (e * (e * (e * 39421680))))))) + (e * (e * (e * (e * (e * (e * 5058890))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 4356180) + (e * 15246630))) + (e * (e * 31751130)))) + (e * (e * (e * 41261250))))) + (e * (e * (e * (e * 32969690)))))) + (e * (e * (e * (e * (e * 15816600))))))) + (e * (e * (e * (e * (e * (e * 4204860)))))))) + (e * (e * (e * (e * (e * (e * (e * 478690)))))))))

private theorem strong4_part_2_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_1 c d e := by
  unfold strong4_part_2_1
  positivity

theorem strong4_part_2_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 1 = strong4_part_2_1 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_1 <;> ring

def strong4_part_2_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 115745920) + ((d * 470446920) + (e * 253650330)))) + ((d * ((d * 880378875) + (e * 956391530))) + (e * (e * 326738295))))) + ((d * ((d * ((d * 922139450) + (e * 1491391490))) + (e * (e * 1026903150)))) + (e * (e * (e * 254942940)))))) + ((d * ((d * ((d * ((d * 553642530) + (e * 1173463950))) + (e * (e * 1211118115)))) + (e * (e * (e * 605728160))))) + (e * (e * (e * (e * 114153685))))))) + ((d * ((d * ((d * ((d * ((d * 178209630) + (e * 460428630))) + (e * (e * 629810190)))) + (e * (e * (e * 475881070))))) + (e * (e * (e * (e * 182278750)))))) + (e * (e * (e * (e * (e * 27672240)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 23908570) + (e * 71725710))) + (e * (e * 121409715)))) + (e * (e * (e * 123276580))))) + (e * (e * (e * (e * 72111375)))))) + (e * (e * (e * (e * (e * 22427370))))))) + (e * (e * (e * (e * (e * (e * 2879895))))))))

private theorem strong4_part_2_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_2 c d e := by
  unfold strong4_part_2_2
  positivity

theorem strong4_part_2_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 2 = strong4_part_2_2 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_2 <;> ring

def strong4_part_2_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 257388470) + ((d * 865882350) + (e * 457343610)))) + ((d * ((d * 1308165570) + (e * 1390265880))) + (e * (e * 479727820))))) + ((d * ((d * ((d * 1047875260) + (e * 1651113120))) + (e * (e * 1137362590)))) + (e * (e * (e * 286354250)))))) + ((d * ((d * ((d * ((d * 429713350) + (e * 883673220))) + (e * (e * 903364760)))) + (e * (e * (e * 454693220))))) + (e * (e * (e * (e * 86391430))))))) + ((d * ((d * ((d * ((d * ((d * 70989280) + (e * 177473200))) + (e * (e * 238121100)))) + (e * (e * (e * 179708450))))) + (e * (e * (e * (e * 69112270)))))) + (e * (e * (e * (e * (e * 10520500)))))))

private theorem strong4_part_2_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_3 c d e := by
  unfold strong4_part_2_3
  positivity

theorem strong4_part_2_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 3 = strong4_part_2_3 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_3 <;> ring

def strong4_part_2_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 358430790) + ((d * 960550140) + (e * 496447250)))) + ((d * ((d * 1101110590) + (e * 1144041040))) + (e * (e * 399003375))))) + ((d * ((d * ((d * 600515750) + (e * 922238850))) + (e * (e * 634692190)))) + (e * (e * (e * 161777590)))))) + ((d * ((d * ((d * ((d * 126120075) + (e * 252240150))) + (e * (e * 254906665)))) + (e * (e * (e * 128786590))))) + (e * (e * (e * (e * 24595565))))))

private theorem strong4_part_2_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_4 c d e := by
  unfold strong4_part_2_4
  positivity

theorem strong4_part_2_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 4 = strong4_part_2_4 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_4 <;> ring

def strong4_part_2_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 323169180) + ((d * 648096630) + (e * 328341360)))) + ((d * ((d * 501074190) + (e * 509660280))) + (e * (e * 179560650))))) + ((d * ((d * ((d * 139310240) + (e * 208965360))) + (e * (e * 143328120)))) + (e * (e * (e * 36836500)))))

private theorem strong4_part_2_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_5 c d e := by
  unfold strong4_part_2_5
  positivity

theorem strong4_part_2_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 5 = strong4_part_2_5 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_5 <;> ring

def strong4_part_2_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * 187333105) + ((d * 250168200) + (e * 125084100)))) + ((d * ((d * 97369610) + (e * 97369610))) + (e * (e * 34534515))))

private theorem strong4_part_2_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_6 c d e := by
  unfold strong4_part_2_6
  positivity

theorem strong4_part_2_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 6 = strong4_part_2_6 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_6 <;> ring

def strong4_part_2_7 (c d e : ℝ) : ℝ :=
  ((c * 65485110) + ((d * 43656740) + (e * 21828370)))

private theorem strong4_part_2_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_7 c d e := by
  unfold strong4_part_2_7
  positivity

theorem strong4_part_2_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 7 = strong4_part_2_7 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_7 <;> ring

def strong4_part_2_8 (c d e : ℝ) : ℝ :=
  10914185

private theorem strong4_part_2_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_2_8 c d e := by
  unfold strong4_part_2_8
  positivity

theorem strong4_part_2_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 2) 8 = strong4_part_2_8 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_2_8 <;> ring

theorem strong4_coeff_2_length (c d e : ℝ) :
    (chamberPoly4 c d e 2).length ≤ 9 := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong4_coeff_2_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly4 c d e 2) b := by
  apply polyEval_nonneg_of_coeff _ b 9
    (strong4_coeff_2_length c d e) hb
  apply forall_fin9
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 0
    rw [strong4_part_2_0_eq]
    exact strong4_part_2_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 1
    rw [strong4_part_2_1_eq]
    exact strong4_part_2_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 2
    rw [strong4_part_2_2_eq]
    exact strong4_part_2_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 3
    rw [strong4_part_2_3_eq]
    exact strong4_part_2_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 4
    rw [strong4_part_2_4_eq]
    exact strong4_part_2_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 5
    rw [strong4_part_2_5_eq]
    exact strong4_part_2_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 6
    rw [strong4_part_2_6_eq]
    exact strong4_part_2_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 7
    rw [strong4_part_2_7_eq]
    exact strong4_part_2_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 2) 8
    rw [strong4_part_2_8_eq]
    exact strong4_part_2_8_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
