module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a^2`

Generated certificate. The coefficient of `a^2` (a power of the smallest weight) in the chamber
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

def strong5_part_2_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 3298205) + ((d * 18285710) + (e * 8099930)))) + ((d * ((d * 47604275) + (e * 41523150))) + (e * (e * 11954045))))) + ((d * ((d * ((d * 72750900) + (e * 94745690))) + (e * (e * 56018950)))) + (e * (e * (e * 13574320)))))) + ((d * ((d * ((d * ((d * 69859825) + (e * 121912050))) + (e * (e * 111361950)))) + (e * (e * (e * 55404900))))) + (e * (e * (e * (e * 11043950))))))) + ((d * ((d * ((d * ((d * ((d * 42723780) + (e * 94551670))) + (e * (e * 119211810)))) + (e * (e * (e * 91003790))))) + (e * (e * (e * (e * 36780880)))))) + (e * (e * (e * (e * (e * 5991650)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 16182515) + (e * 44080220))) + (e * (e * 72386170)))) + (e * (e * (e * 75293610))))) + (e * (e * (e * (e * 46122555)))))) + (e * (e * (e * (e * (e * 15164280))))))) + (e * (e * (e * (e * (e * (e * 2075080))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3469070) + (e * 11467060))) + (e * (e * 23707530)))) + (e * (e * (e * 31478770))))) + (e * (e * (e * (e * 25923350)))))) + (e * (e * (e * (e * (e * 12860310))))))) + (e * (e * (e * (e * (e * (e * 3547670)))))))) + (e * (e * (e * (e * (e * (e * (e * 420740)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 322745) + (e * 1290980))) + (e * (e * 3285340)))) + (e * (e * (e * 5337590))))) + (e * (e * (e * (e * 5528370)))))) + (e * (e * (e * (e * (e * 3666900))))))) + (e * (e * (e * (e * (e * (e * 1521805)))))))) + (e * (e * (e * (e * (e * (e * (e * 362790))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 38105))))))))))

private theorem strong5_part_2_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_0 c d e := by
  unfold strong5_part_2_0
  positivity

theorem strong5_part_2_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 0 = strong5_part_2_0 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_0 <;> ring

def strong5_part_2_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 29641340) + ((d * 141931150) + (e * 64019080)))) + ((d * ((d * 317026750) + (e * 282688920))) + (e * (e * 84635840))))) + ((d * ((d * ((d * 408463430) + (e * 547918740))) + (e * (e * 336343500)))) + (e * (e * (e * 82887790)))))) + ((d * ((d * ((d * ((d * 319755730) + (e * 579815460))) + (e * (e * 548108430)))) + (e * (e * (e * 275000740))))) + (e * (e * (e * (e * 54267990))))))) + ((d * ((d * ((d * ((d * ((d * 150349570) + (e * 348753020))) + (e * (e * 452484030)))) + (e * (e * (e * 345077950))))) + (e * (e * (e * (e * 137147810)))))) + (e * (e * (e * (e * (e * 21808560)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 39155200) + (e * 112579060))) + (e * (e * 188571190)))) + (e * (e * (e * 193976840))))) + (e * (e * (e * (e * 116048900)))))) + (e * (e * (e * (e * (e * 37066260))))))) + (e * (e * (e * (e * (e * (e * 4905760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 4356180) + (e * 15246630))) + (e * (e * 31751130)))) + (e * (e * (e * 41261250))))) + (e * (e * (e * (e * 32969690)))))) + (e * (e * (e * (e * (e * 15816600))))))) + (e * (e * (e * (e * (e * (e * 4204860)))))))) + (e * (e * (e * (e * (e * (e * (e * 478690)))))))))

private theorem strong5_part_2_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_1 c d e := by
  unfold strong5_part_2_1
  positivity

theorem strong5_part_2_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 1 = strong5_part_2_1 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_1 <;> ring

def strong5_part_2_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 115745920) + ((d * 470446920) + (e * 216796590)))) + ((d * ((d * 880378875) + (e * 804366220))) + (e * (e * 250725640))))) + ((d * ((d * ((d * 922139450) + (e * 1275026860))) + (e * (e * 810538520)))) + (e * (e * (e * 202708170)))))) + ((d * ((d * ((d * ((d * 553642530) + (e * 1041106170))) + (e * (e * 1012581445)))) + (e * (e * (e * 510686340))))) + (e * (e * (e * (e * 99722220))))))) + ((d * ((d * ((d * ((d * ((d * 178209630) + (e * 430619520))) + (e * (e * 570191970)))) + (e * (e * (e * 433074020))))) + (e * (e * (e * (e * 169280810)))))) + (e * (e * (e * (e * (e * 26316630)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 23908570) + (e * 71725710))) + (e * (e * 121409715)))) + (e * (e * (e * 123276580))))) + (e * (e * (e * (e * 72111375)))))) + (e * (e * (e * (e * (e * 22427370))))))) + (e * (e * (e * (e * (e * (e * 2879895))))))))

private theorem strong5_part_2_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_2 c d e := by
  unfold strong5_part_2_2
  positivity

theorem strong5_part_2_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 2 = strong5_part_2_2 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_2 <;> ring

def strong5_part_2_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 257388470) + ((d * 865882350) + (e * 408538740)))) + ((d * ((d * 1308165570) + (e * 1226065260))) + (e * (e * 397627510))))) + ((d * ((d * ((d * 1047875260) + (e * 1492512660))) + (e * (e * 978762130)))) + (e * (e * (e * 247770480)))))) + ((d * ((d * ((d * ((d * 429713350) + (e * 835180180))) + (e * (e * 830625200)))) + (e * (e * (e * 419870040))))) + (e * (e * (e * (e * 81103100))))))) + ((d * ((d * ((d * ((d * ((d * 70989280) + (e * 177473200))) + (e * (e * 238121100)))) + (e * (e * (e * 179708450))))) + (e * (e * (e * (e * 69112270)))))) + (e * (e * (e * (e * (e * 10520500)))))))

private theorem strong5_part_2_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_3 c d e := by
  unfold strong5_part_2_3
  positivity

theorem strong5_part_2_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 3 = strong5_part_2_3 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_3 <;> ring

def strong5_part_2_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 358430790) + ((d * 960550140) + (e * 464102890)))) + ((d * ((d * 1101110590) + (e * 1058180140))) + (e * (e * 356072925))))) + ((d * ((d * ((d * 600515750) + (e * 879308400))) + (e * (e * 591761740)))) + (e * (e * (e * 151191500)))))) + ((d * ((d * ((d * ((d * 126120075) + (e * 252240150))) + (e * (e * 254906665)))) + (e * (e * (e * 128786590))))) + (e * (e * (e * (e * 24595565))))))

private theorem strong5_part_2_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_4 c d e := by
  unfold strong5_part_2_4
  positivity

theorem strong5_part_2_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 4 = strong5_part_2_4 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_4 <;> ring

def strong5_part_2_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 323169180) + ((d * 648096630) + (e * 319755270)))) + ((d * ((d * 501074190) + (e * 492488100))) + (e * (e * 170974560))))) + ((d * ((d * ((d * 139310240) + (e * 208965360))) + (e * (e * 143328120)))) + (e * (e * (e * 36836500)))))

private theorem strong5_part_2_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_5 c d e := by
  unfold strong5_part_2_5
  positivity

theorem strong5_part_2_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 5 = strong5_part_2_5 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_5 <;> ring

def strong5_part_2_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * 187333105) + ((d * 250168200) + (e * 125084100)))) + ((d * ((d * 97369610) + (e * 97369610))) + (e * (e * 34534515))))

private theorem strong5_part_2_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_6 c d e := by
  unfold strong5_part_2_6
  positivity

theorem strong5_part_2_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 6 = strong5_part_2_6 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_6 <;> ring

def strong5_part_2_7 (c d e : ℝ) : ℝ :=
  ((c * 65485110) + ((d * 43656740) + (e * 21828370)))

private theorem strong5_part_2_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_7 c d e := by
  unfold strong5_part_2_7
  positivity

theorem strong5_part_2_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 7 = strong5_part_2_7 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_7 <;> ring

def strong5_part_2_8 (c d e : ℝ) : ℝ :=
  10914185

private theorem strong5_part_2_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_2_8 c d e := by
  unfold strong5_part_2_8
  positivity

theorem strong5_part_2_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 2) 8 = strong5_part_2_8 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_2_8 <;> ring

theorem strong5_coeff_2_length (c d e : ℝ) :
    (chamberPoly5 c d e 2).length ≤ 9 := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong5_coeff_2_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly5 c d e 2) b := by
  apply polyEval_nonneg_of_coeff _ b 9
    (strong5_coeff_2_length c d e) hb
  apply forall_fin9
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 0
    rw [strong5_part_2_0_eq]
    exact strong5_part_2_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 1
    rw [strong5_part_2_1_eq]
    exact strong5_part_2_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 2
    rw [strong5_part_2_2_eq]
    exact strong5_part_2_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 3
    rw [strong5_part_2_3_eq]
    exact strong5_part_2_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 4
    rw [strong5_part_2_4_eq]
    exact strong5_part_2_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 5
    rw [strong5_part_2_5_eq]
    exact strong5_part_2_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 6
    rw [strong5_part_2_6_eq]
    exact strong5_part_2_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 7
    rw [strong5_part_2_7_eq]
    exact strong5_part_2_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 2) 8
    rw [strong5_part_2_8_eq]
    exact strong5_part_2_8_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
