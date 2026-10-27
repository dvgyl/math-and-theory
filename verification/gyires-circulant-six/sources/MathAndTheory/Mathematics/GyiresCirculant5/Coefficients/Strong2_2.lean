module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a^2`

Generated certificate. The coefficient of `a^2` (a power of the smallest weight) in the chamber
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

def strong2_part_2_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 3298205) + ((d * 16199860) + (e * 8099930)))) + ((d * ((d * 39084450) + (e * 39084450))) + (e * (e * 11954045))))) + ((d * ((d * ((d * 58559280) + (e * 87838920))) + (e * (e * 56428280)))) + (e * (e * (e * 13574320)))))) + ((d * ((d * ((d * ((d * 57599175) + (e * 115198350))) + (e * (e * 114241675)))) + (e * (e * (e * 56642500))))) + (e * (e * (e * (e * 11043950))))))) + ((d * ((d * ((d * ((d * ((d * 37027920) + (e * 92569800))) + (e * (e * 124795580)))) + (e * (e * (e * 94623570))))) + (e * (e * (e * (e * 37353170)))))) + (e * (e * (e * (e * (e * 5991650)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 14890290) + (e * 44670870))) + (e * (e * 76632885)))) + (e * (e * (e * 78814320))))) + (e * (e * (e * (e * 47223165)))))) + (e * (e * (e * (e * (e * 15261150))))))) + (e * (e * (e * (e * (e * (e * 2075080))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3369700) + (e * 11793950))) + (e * (e * 24840870)))) + (e * (e * (e * 32617300))))) + (e * (e * (e * (e * 26451670)))))) + (e * (e * (e * (e * (e * 12957180))))))) + (e * (e * (e * (e * (e * (e * 3547670)))))))) + (e * (e * (e * (e * (e * (e * (e * 420740)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 322745) + (e * 1290980))) + (e * (e * 3285340)))) + (e * (e * (e * 5337590))))) + (e * (e * (e * (e * 5528370)))))) + (e * (e * (e * (e * (e * 3666900))))))) + (e * (e * (e * (e * (e * (e * 1521805)))))))) + (e * (e * (e * (e * (e * (e * (e * 362790))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 38105))))))))))

private theorem strong2_part_2_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_0 c d e := by
  unfold strong2_part_2_0
  positivity

theorem strong2_part_2_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 0 = strong2_part_2_0 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_0 <;> ring

def strong2_part_2_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 29641340) + ((d * 129577310) + (e * 65558230)))) + ((d * ((d * 273969390) + (e * 277241540))) + (e * (e * 87907990))))) + ((d * ((d * ((d * 349633800) + (e * 531806290))) + (e * (e * 350210250)))) + (e * (e * (e * 85149970)))))) + ((d * ((d * ((d * ((d * 280256550) + (e * 570765420))) + (e * (e * 575108990)))) + (e * (e * (e * 285325540))))) + (e * (e * (e * (e * 54993410))))))) + ((d * ((d * ((d * ((d * ((d * 137127360) + (e * 351268550))) + (e * (e * 478169230)))) + (e * (e * (e * 360057280))))) + (e * (e * (e * (e * 139743230)))))) + (e * (e * (e * (e * (e * 21905430)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 37206690) + (e * 115345600))) + (e * (e * 198983770)))) + (e * (e * (e * 202032080))))) + (e * (e * (e * (e * 118447220)))))) + (e * (e * (e * (e * (e * 37260000))))))) + (e * (e * (e * (e * (e * (e * 4905760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 4256810) + (e * 15573520))) + (e * (e * 32884470)))) + (e * (e * (e * 42399780))))) + (e * (e * (e * (e * 33498010)))))) + (e * (e * (e * (e * (e * 15913470))))))) + (e * (e * (e * (e * (e * (e * 4204860)))))))) + (e * (e * (e * (e * (e * (e * (e * 478690)))))))))

private theorem strong2_part_2_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_1 c d e := by
  unfold strong2_part_2_1
  positivity

theorem strong2_part_2_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 1 = strong2_part_2_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_1 <;> ring

def strong2_part_2_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 115745920) + ((d * 440825190) + (e * 224028600)))) + ((d * ((d * 794675445) + (e * 808282880))) + (e * (e * 264333075))))) + ((d * ((d * ((d * 830425340) + (e * 1272895550))) + (e * (e * 855003630)))) + (e * (e * (e * 209825250)))))) + ((d * ((d * ((d * ((d * 509440135) + (e * 1050174710))) + (e * (e * 1069850875)))) + (e * (e * (e * 530611110))))) + (e * (e * (e * (e * 101217030))))))) + ((d * ((d * ((d * ((d * ((d * 168983360) + (e * 440679910))) + (e * (e * 602769590)))) + (e * (e * (e * 450416240))))) + (e * (e * (e * (e * 172073330)))))) + (e * (e * (e * (e * (e * 26413500)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 23252285) + (e * 73901600))) + (e * (e * 127575580)))) + (e * (e * (e * 127811110))))) + (e * (e * (e * (e * 73409085)))))) + (e * (e * (e * (e * (e * 22524240))))))) + (e * (e * (e * (e * (e * (e * 2879895))))))))

private theorem strong2_part_2_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_2 c d e := by
  unfold strong2_part_2_2
  positivity

theorem strong2_part_2_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 2 = strong2_part_2_2 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_2 <;> ring

def strong2_part_2_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 257388470) + ((d * 829598740) + (e * 421060000)))) + ((d * ((d * 1224238080) + (e * 1245131440))) + (e * (e * 418520870))))) + ((d * ((d * ((d * 982652250) + (e * 1510855190))) + (e * (e * 1031185470)))) + (e * (e * (e * 255212050)))))) + ((d * ((d * ((d * ((d * 410434300) + (e * 852540780))) + (e * (e * 874631370)))) + (e * (e * (e * 433294280))))) + (e * (e * (e * (e * 81872490))))))) + ((d * ((d * ((d * ((d * ((d * 69289360) + (e * 183036190))) + (e * (e * 250597290)))) + (e * (e * (e * 185691120))))) + (e * (e * (e * (e * 69881660)))))) + (e * (e * (e * (e * (e * 10520500)))))))

private theorem strong2_part_2_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_3 c d e := by
  unfold strong2_part_2_3
  positivity

theorem strong2_part_2_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 3 = strong2_part_2_3 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_3 <;> ring

def strong2_part_2_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 358430790) + ((d * 937275910) + (e * 473173020)))) + ((d * ((d * 1060246365) + (e * 1074218350))) + (e * (e * 370044910))))) + ((d * ((d * ((d * 580610570) + (e * 892232200))) + (e * (e * 616591300)))) + (e * (e * (e * 153778170)))))) + ((d * ((d * ((d * ((d * 123804890) + (e * 258195870))) + (e * (e * 265764240)))) + (e * (e * (e * 131373260))))) + (e * (e * (e * (e * 24595565))))))

private theorem strong2_part_2_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_4 c d e := by
  unfold strong2_part_2_4
  positivity

theorem strong2_part_2_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 4 = strong2_part_2_4 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_4 <;> ring

def strong2_part_2_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 323169180) + ((d * 641166180) + (e * 321410910)))) + ((d * ((d * 492385470) + (e * 495799380))) + (e * (e * 174388470))))) + ((d * ((d * ((d * 137551970) + (e * 210621000))) + (e * (e * 146742030)))) + (e * (e * (e * 36836500)))))

private theorem strong2_part_2_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_5 c d e := by
  unfold strong2_part_2_5
  positivity

theorem strong2_part_2_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 5 = strong2_part_2_5 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_5 <;> ring

def strong2_part_2_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * 187333105) + ((d * 249582110) + (e * 124498010)))) + ((d * ((d * 96783520) + (e * 96783520))) + (e * (e * 34534515))))

private theorem strong2_part_2_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_6 c d e := by
  unfold strong2_part_2_6
  positivity

theorem strong2_part_2_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 6 = strong2_part_2_6 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_6 <;> ring

def strong2_part_2_7 (c d e : ℝ) : ℝ :=
  ((c * 65485110) + ((d * 43656740) + (e * 21828370)))

private theorem strong2_part_2_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_7 c d e := by
  unfold strong2_part_2_7
  positivity

theorem strong2_part_2_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 7 = strong2_part_2_7 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_7 <;> ring

def strong2_part_2_8 (c d e : ℝ) : ℝ :=
  10914185

private theorem strong2_part_2_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_2_8 c d e := by
  unfold strong2_part_2_8
  positivity

theorem strong2_part_2_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 2) 8 = strong2_part_2_8 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_2_8 <;> ring

theorem strong2_coeff_2_length (c d e : ℝ) :
    (chamberPoly2 c d e 2).length ≤ 9 := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong2_coeff_2_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly2 c d e 2) b := by
  apply polyEval_nonneg_of_coeff _ b 9
    (strong2_coeff_2_length c d e) hb
  apply forall_fin9
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 0
    rw [strong2_part_2_0_eq]
    exact strong2_part_2_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 1
    rw [strong2_part_2_1_eq]
    exact strong2_part_2_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 2
    rw [strong2_part_2_2_eq]
    exact strong2_part_2_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 3
    rw [strong2_part_2_3_eq]
    exact strong2_part_2_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 4
    rw [strong2_part_2_4_eq]
    exact strong2_part_2_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 5
    rw [strong2_part_2_5_eq]
    exact strong2_part_2_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 6
    rw [strong2_part_2_6_eq]
    exact strong2_part_2_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 7
    rw [strong2_part_2_7_eq]
    exact strong2_part_2_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 2) 8
    rw [strong2_part_2_8_eq]
    exact strong2_part_2_8_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
