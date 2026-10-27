module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a^2`

Generated certificate. The coefficient of `a^2` (a power of the smallest weight) in the chamber
polynomial `chamberPoly3` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong3_part_2_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 3298205) + ((d * 16199860) + (e * 8099930)))) + ((d * ((d * 39084450) + (e * 39084450))) + (e * (e * 11954045))))) + ((d * ((d * ((d * 58559280) + (e * 87838920))) + (e * (e * 56428280)))) + (e * (e * (e * 13574320)))))) + ((d * ((d * ((d * ((d * 57599175) + (e * 115198350))) + (e * (e * 114241675)))) + (e * (e * (e * 56642500))))) + (e * (e * (e * (e * 11043950))))))) + ((d * ((d * ((d * ((d * ((d * 37027920) + (e * 92569800))) + (e * (e * 124795580)))) + (e * (e * (e * 94623570))))) + (e * (e * (e * (e * 37353170)))))) + (e * (e * (e * (e * (e * 5991650)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 14890290) + (e * 44670870))) + (e * (e * 76632885)))) + (e * (e * (e * 78814320))))) + (e * (e * (e * (e * 47223165)))))) + (e * (e * (e * (e * (e * 15261150))))))) + (e * (e * (e * (e * (e * (e * 2075080))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3369700) + (e * 11793950))) + (e * (e * 24840870)))) + (e * (e * (e * 32617300))))) + (e * (e * (e * (e * 26451670)))))) + (e * (e * (e * (e * (e * 12957180))))))) + (e * (e * (e * (e * (e * (e * 3547670)))))))) + (e * (e * (e * (e * (e * (e * (e * 420740)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 322745) + (e * 1290980))) + (e * (e * 3285340)))) + (e * (e * (e * 5337590))))) + (e * (e * (e * (e * 5528370)))))) + (e * (e * (e * (e * (e * 3666900))))))) + (e * (e * (e * (e * (e * (e * 1521805)))))))) + (e * (e * (e * (e * (e * (e * (e * 362790))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 38105))))))))))

private theorem strong3_part_2_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_0 c d e := by
  unfold strong3_part_2_0
  positivity

theorem strong3_part_2_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 0 = strong3_part_2_0 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_0 <;> ring

def strong3_part_2_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 29641340) + ((d * 129577310) + (e * 64019080)))) + ((d * ((d * 273969390) + (e * 270697240))) + (e * (e * 84635840))))) + ((d * ((d * ((d * 349633800) + (e * 517095110))) + (e * (e * 335499070)))) + (e * (e * (e * 82887790)))))) + ((d * ((d * ((d * ((d * 280256550) + (e * 550260780))) + (e * (e * 544352030)))) + (e * (e * (e * 273622380))))) + (e * (e * (e * (e * 54267990))))))) + ((d * ((d * ((d * ((d * ((d * 137127360) + (e * 334368250))) + (e * (e * 444368630)))) + (e * (e * (e * 338112710))))) + (e * (e * (e * (e * 134698960)))))) + (e * (e * (e * (e * (e * 21808560)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 37206690) + (e * 107894540))) + (e * (e * 180356120)))) + (e * (e * (e * 184580800))))) + (e * (e * (e * (e * 110897950)))))) + (e * (e * (e * (e * (e * 35985420))))))) + (e * (e * (e * (e * (e * (e * 4905760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 4256810) + (e * 14224150))) + (e * (e * 28836360)))) + (e * (e * (e * 37408120))))) + (e * (e * (e * (e * 30261540)))))) + (e * (e * (e * (e * (e * 14816790))))))) + (e * (e * (e * (e * (e * (e * 4051730)))))))) + (e * (e * (e * (e * (e * (e * (e * 478690)))))))))

private theorem strong3_part_2_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_1 c d e := by
  unfold strong3_part_2_1
  positivity

theorem strong3_part_2_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 1 = strong3_part_2_1 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_1 <;> ring

def strong3_part_2_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 115745920) + ((d * 440825190) + (e * 216796590)))) + ((d * ((d * 794675445) + (e * 781068010))) + (e * (e * 250725640))))) + ((d * ((d * ((d * 830425340) + (e * 1218380470))) + (e * (e * 800488550)))) + (e * (e * (e * 202708170)))))) + ((d * ((d * ((d * ((d * 509440135) + (e * 987585830))) + (e * (e * 975967555)))) + (e * (e * (e * 496327050))))) + (e * (e * (e * (e * 99722220))))))) + ((d * ((d * ((d * ((d * ((d * 168983360) + (e * 404236890))) + (e * (e * 529883550)))) + (e * (e * (e * 403646670))))) + (e * (e * (e * (e * 161746780)))))) + (e * (e * (e * (e * (e * 26316630)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 23252285) + (e * 65612110))) + (e * (e * 106851855)))) + (e * (e * (e * 108520910))))) + (e * (e * (e * (e * 65197510)))))) + (e * (e * (e * (e * (e * 21168630))))))) + (e * (e * (e * (e * (e * (e * 2879895))))))))

private theorem strong3_part_2_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_2 c d e := by
  unfold strong3_part_2_2
  positivity

theorem strong3_part_2_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 2 = strong3_part_2_2 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_2 <;> ring

def strong3_part_2_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 257388470) + ((d * 829598740) + (e * 408538740)))) + ((d * ((d * 1224238080) + (e * 1203344720))) + (e * (e * 397627510))))) + ((d * ((d * ((d * 982652250) + (e * 1437101560))) + (e * (e * 957431840)))) + (e * (e * (e * 247770480)))))) + ((d * ((d * ((d * ((d * 410434300) + (e * 789196420))) + (e * (e * 779614830)))) + (e * (e * (e * 400083320))))) + (e * (e * (e * (e * 81103100))))))) + ((d * ((d * ((d * ((d * ((d * 69289360) + (e * 163410610))) + (e * (e * 211346130)))) + (e * (e * (e * 160777210))))) + (e * (e * (e * (e * 64593330)))))) + (e * (e * (e * (e * (e * 10520500)))))))

private theorem strong3_part_2_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_3 c d e := by
  unfold strong3_part_2_3
  positivity

theorem strong3_part_2_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 3 = strong3_part_2_3 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_3 <;> ring

def strong3_part_2_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 358430790) + ((d * 937275910) + (e * 464102890)))) + ((d * ((d * 1060246365) + (e * 1046274380))) + (e * (e * 356072925))))) + ((d * ((d * ((d * 580610570) + (e * 849599510))) + (e * (e * 573958610)))) + (e * (e * (e * 151191500)))))) + ((d * ((d * ((d * ((d * 123804890) + (e * 237023690))) + (e * (e * 234005970)))) + (e * (e * (e * 120787170))))) + (e * (e * (e * (e * 24595565))))))

private theorem strong3_part_2_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_4 c d e := by
  unfold strong3_part_2_4
  positivity

theorem strong3_part_2_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 4 = strong3_part_2_4 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_4 <;> ring

def strong3_part_2_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 323169180) + ((d * 641166180) + (e * 319755270)))) + ((d * ((d * 492385470) + (e * 488971560))) + (e * (e * 170974560))))) + ((d * ((d * ((d * 137551970) + (e * 202034910))) + (e * (e * 138155940)))) + (e * (e * (e * 36836500)))))

private theorem strong3_part_2_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_5 c d e := by
  unfold strong3_part_2_5
  positivity

theorem strong3_part_2_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 5 = strong3_part_2_5 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_5 <;> ring

def strong3_part_2_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * 187333105) + ((d * 249582110) + (e * 125084100)))) + ((d * ((d * 96783520) + (e * 96783520))) + (e * (e * 34534515))))

private theorem strong3_part_2_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_6 c d e := by
  unfold strong3_part_2_6
  positivity

theorem strong3_part_2_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 6 = strong3_part_2_6 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_6 <;> ring

def strong3_part_2_7 (c d e : ℝ) : ℝ :=
  ((c * 65485110) + ((d * 43656740) + (e * 21828370)))

private theorem strong3_part_2_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_7 c d e := by
  unfold strong3_part_2_7
  positivity

theorem strong3_part_2_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 7 = strong3_part_2_7 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_7 <;> ring

def strong3_part_2_8 (c d e : ℝ) : ℝ :=
  10914185

private theorem strong3_part_2_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_2_8 c d e := by
  unfold strong3_part_2_8
  positivity

theorem strong3_part_2_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 2) 8 = strong3_part_2_8 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_2_8 <;> ring

theorem strong3_coeff_2_length (c d e : ℝ) :
    (chamberPoly3 c d e 2).length ≤ 9 := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num

theorem strong3_coeff_2_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly3 c d e 2) b := by
  apply polyEval_nonneg_of_coeff _ b 9
    (strong3_coeff_2_length c d e) hb
  apply forall_fin9
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 0
    rw [strong3_part_2_0_eq]
    exact strong3_part_2_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 1
    rw [strong3_part_2_1_eq]
    exact strong3_part_2_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 2
    rw [strong3_part_2_2_eq]
    exact strong3_part_2_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 3
    rw [strong3_part_2_3_eq]
    exact strong3_part_2_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 4
    rw [strong3_part_2_4_eq]
    exact strong3_part_2_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 5
    rw [strong3_part_2_5_eq]
    exact strong3_part_2_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 6
    rw [strong3_part_2_6_eq]
    exact strong3_part_2_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 7
    rw [strong3_part_2_7_eq]
    exact strong3_part_2_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 2) 8
    rw [strong3_part_2_8_eq]
    exact strong3_part_2_8_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
