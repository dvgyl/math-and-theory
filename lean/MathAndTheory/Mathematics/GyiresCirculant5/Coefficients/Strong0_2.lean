module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a^2`

Generated certificate. The coefficient of `a^2` (a power of the smallest weight) in the chamber
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

def strong0_part_2_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 3298205) + ((d * 18285710) + (e * 8099930)))) + ((d * ((d * 47604275) + (e * 41523150))) + (e * (e * 11954045))))) + ((d * ((d * ((d * 72750900) + (e * 94745690))) + (e * (e * 56018950)))) + (e * (e * (e * 13574320)))))) + ((d * ((d * ((d * ((d * 69859825) + (e * 121912050))) + (e * (e * 111361950)))) + (e * (e * (e * 55404900))))) + (e * (e * (e * (e * 11043950))))))) + ((d * ((d * ((d * ((d * ((d * 42723780) + (e * 94551670))) + (e * (e * 119211810)))) + (e * (e * (e * 91003790))))) + (e * (e * (e * (e * 36780880)))))) + (e * (e * (e * (e * (e * 5991650)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 16182515) + (e * 44080220))) + (e * (e * 72386170)))) + (e * (e * (e * 75293610))))) + (e * (e * (e * (e * 46122555)))))) + (e * (e * (e * (e * (e * 15164280))))))) + (e * (e * (e * (e * (e * (e * 2075080))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3469070) + (e * 11467060))) + (e * (e * 23707530)))) + (e * (e * (e * 31478770))))) + (e * (e * (e * (e * 25923350)))))) + (e * (e * (e * (e * (e * 12860310))))))) + (e * (e * (e * (e * (e * (e * 3547670)))))))) + (e * (e * (e * (e * (e * (e * (e * 420740)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 322745) + (e * 1290980))) + (e * (e * 3285340)))) + (e * (e * (e * 5337590))))) + (e * (e * (e * (e * 5528370)))))) + (e * (e * (e * (e * (e * 3666900))))))) + (e * (e * (e * (e * (e * (e * 1521805)))))))) + (e * (e * (e * (e * (e * (e * (e * 362790))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 38105))))))))))

private theorem strong0_part_2_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_0 c d e := by
  unfold strong0_part_2_0
  positivity

theorem strong0_part_2_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 0 = strong0_part_2_0 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_0 <;> ring

def strong0_part_2_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 29641340) + ((d * 143470300) + (e * 65558230)))) + ((d * ((d * 322989500) + (e * 291923820))) + (e * (e * 87907990))))) + ((d * ((d * ((d * 417452110) + (e * 563081350))) + (e * (e * 344779610)))) + (e * (e * (e * 85149970)))))) + ((d * ((d * ((d * ((d * 326140530) + (e * 587701380))) + (e * (e * 549131370)))) + (e * (e * (e * 275247980))))) + (e * (e * (e * (e * 54993410))))))) + ((d * ((d * ((d * ((d * ((d * 152209010) + (e * 346136950))) + (e * (e * 440393880)))) + (e * (e * (e * 334982780))))) + (e * (e * (e * (e * 134764150)))))) + (e * (e * (e * (e * (e * 21905430)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 39095550) + (e * 108674580))) + (e * (e * 177529390)))) + (e * (e * (e * 182093500))))) + (e * (e * (e * (e * 110281690)))))) + (e * (e * (e * (e * (e * 35985420))))))) + (e * (e * (e * (e * (e * (e * 4905760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 4256810) + (e * 14224150))) + (e * (e * 28836360)))) + (e * (e * (e * 37408120))))) + (e * (e * (e * (e * 30261540)))))) + (e * (e * (e * (e * (e * 14816790))))))) + (e * (e * (e * (e * (e * (e * 4051730)))))))) + (e * (e * (e * (e * (e * (e * (e * 478690)))))))))

private theorem strong0_part_2_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_1 c d e := by
  unfold strong0_part_2_1
  positivity

theorem strong0_part_2_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 1 = strong0_part_2_1 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_1 <;> ring

def strong0_part_2_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 115745920) + ((d * 477678930) + (e * 224028600)))) + ((d * ((d * 902931490) + (e * 840526270))) + (e * (e * 264333075))))) + ((d * ((d * ((d * 947146890) + (e * 1314183120))) + (e * (e * 831804420)))) + (e * (e * (e * 209825250)))))) + ((d * ((d * ((d * ((d * 564174450) + (e * 1042239570))) + (e * (e * 994734535)))) + (e * (e * (e * 503732760))))) + (e * (e * (e * (e * 101217030))))))) + ((d * ((d * ((d * ((d * ((d * 178398430) + (e * 414055490))) + (e * (e * 531562260)))) + (e * (e * (e * 404247690))))) + (e * (e * (e * (e * 162428230)))))) + (e * (e * (e * (e * (e * 26413500)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 23252285) + (e * 65612110))) + (e * (e * 106851855)))) + (e * (e * (e * 108520910))))) + (e * (e * (e * (e * 65197510)))))) + (e * (e * (e * (e * (e * 21168630))))))) + (e * (e * (e * (e * (e * (e * 2879895))))))))

private theorem strong0_part_2_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_2 c d e := by
  unfold strong0_part_2_2
  positivity

theorem strong0_part_2_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 2 = strong0_part_2_2 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_2 <;> ring

def strong0_part_2_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 257388470) + ((d * 878403610) + (e * 421060000)))) + ((d * ((d * 1337357250) + (e * 1276150300))) + (e * (e * 418520870))))) + ((d * ((d * ((d * 1067764310) + (e * 1516211300))) + (e * (e * 990013290)))) + (e * (e * (e * 255212050)))))) + ((d * ((d * ((d * ((d * 431232060) + (e * 812540780))) + (e * (e * 790447440)))) + (e * (e * (e * 404619780))))) + (e * (e * (e * (e * 81872490))))))) + ((d * ((d * ((d * ((d * ((d * 69289360) + (e * 163410610))) + (e * (e * 211346130)))) + (e * (e * (e * 160777210))))) + (e * (e * (e * (e * 64593330)))))) + (e * (e * (e * (e * (e * 10520500)))))))

private theorem strong0_part_2_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_3 c d e := by
  unfold strong0_part_2_3
  positivity

theorem strong0_part_2_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 3 = strong0_part_2_3 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_3 <;> ring

def strong0_part_2_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 358430790) + ((d * 969620270) + (e * 473173020)))) + ((d * ((d * 1114348995) + (e * 1085390530))) + (e * (e * 370044910))))) + ((d * ((d * ((d * 602368840) + (e * 871646110))) + (e * (e * 584833030)))) + (e * (e * (e * 153778170)))))) + ((d * ((d * ((d * ((d * 123804890) + (e * 237023690))) + (e * (e * 234005970)))) + (e * (e * (e * 120787170))))) + (e * (e * (e * (e * 24595565))))))

private theorem strong0_part_2_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_4 c d e := by
  unfold strong0_part_2_4
  positivity

theorem strong0_part_2_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 4 = strong0_part_2_4 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_4 <;> ring

def strong0_part_2_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 323169180) + ((d * 649752270) + (e * 321410910)))) + ((d * ((d * 500971560) + (e * 495799380))) + (e * (e * 174388470))))) + ((d * ((d * ((d * 137551970) + (e * 202034910))) + (e * (e * 138155940)))) + (e * (e * (e * 36836500)))))

private theorem strong0_part_2_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_5 c d e := by
  unfold strong0_part_2_5
  positivity

theorem strong0_part_2_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 5 = strong0_part_2_5 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_5 <;> ring

def strong0_part_2_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * 187333105) + ((d * 249582110) + (e * 124498010)))) + ((d * ((d * 96783520) + (e * 96783520))) + (e * (e * 34534515))))

private theorem strong0_part_2_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_6 c d e := by
  unfold strong0_part_2_6
  positivity

theorem strong0_part_2_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 6 = strong0_part_2_6 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_6 <;> ring

def strong0_part_2_7 (c d e : ℝ) : ℝ :=
  ((c * 65485110) + ((d * 43656740) + (e * 21828370)))

private theorem strong0_part_2_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_7 c d e := by
  unfold strong0_part_2_7
  positivity

theorem strong0_part_2_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 7 = strong0_part_2_7 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_7 <;> ring

def strong0_part_2_8 (c d e : ℝ) : ℝ :=
  10914185

private theorem strong0_part_2_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_2_8 c d e := by
  unfold strong0_part_2_8
  positivity

theorem strong0_part_2_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 2) 8 = strong0_part_2_8 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_2_8 <;> ring

theorem strong0_coeff_2_length (c d e : ℝ) :
    (chamberPoly0 c d e 2).length ≤ 9 := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong0_coeff_2_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly0 c d e 2) b := by
  apply polyEval_nonneg_of_coeff _ b 9
    (strong0_coeff_2_length c d e) hb
  apply forall_fin9
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 0
    rw [strong0_part_2_0_eq]
    exact strong0_part_2_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 1
    rw [strong0_part_2_1_eq]
    exact strong0_part_2_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 2
    rw [strong0_part_2_2_eq]
    exact strong0_part_2_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 3
    rw [strong0_part_2_3_eq]
    exact strong0_part_2_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 4
    rw [strong0_part_2_4_eq]
    exact strong0_part_2_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 5
    rw [strong0_part_2_5_eq]
    exact strong0_part_2_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 6
    rw [strong0_part_2_6_eq]
    exact strong0_part_2_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 7
    rw [strong0_part_2_7_eq]
    exact strong0_part_2_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 2) 8
    rw [strong0_part_2_8_eq]
    exact strong0_part_2_8_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
