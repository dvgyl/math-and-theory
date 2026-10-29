module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a^1`

Generated certificate. The coefficient of `a^1` (a power of the smallest weight) in the chamber
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

def strong2_part_1_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 573910) + ((d * 3042420) + (e * 1521210)))) + ((d * ((d * 8017340) + (e * 8017340))) + (e * (e * 2327610))))) + ((d * ((d * ((d * 13443040) + (e * 20164560))) + (e * (e * 12578060)))) + (e * (e * (e * 2928270)))))) + ((d * ((d * ((d * ((d * 15339290) + (e * 30678580))) + (e * (e * 30120810)))) + (e * (e * (e * 14781520))))) + (e * (e * (e * (e * 2863180))))))) + ((d * ((d * ((d * ((d * ((d * 12003620) + (e * 30009050))) + (e * (e * 40720200)))) + (e * (e * (e * 31071250))))) + (e * (e * (e * (e * 12343960)))))) + (e * (e * (e * (e * (e * 1993740)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 6295220) + (e * 18885660))) + (e * (e * 33093610)))) + (e * (e * (e * 34711120))))) + (e * (e * (e * (e * 21182710)))))) + (e * (e * (e * (e * (e * 6974760))))))) + (e * (e * (e * (e * (e * (e * 969960))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2090160) + (e * 7315560))) + (e * (e * 15974580)))) + (e * (e * (e * 21647550))))) + (e * (e * (e * (e * 18081760)))))) + (e * (e * (e * (e * (e * 9132870))))))) + (e * (e * (e * (e * (e * (e * 2591880)))))))) + (e * (e * (e * (e * (e * (e * (e * 321200)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 388870) + (e * 1555480))) + (e * (e * 4180100)))) + (e * (e * (e * 7096120))))) + (e * (e * (e * (e * 7657000)))))) + (e * (e * (e * (e * (e * 5301860))))))) + (e * (e * (e * (e * (e * (e * 2309290)))))))) + (e * (e * (e * (e * (e * (e * (e * 581800))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 29380) + (e * 132210))) + (e * (e * 445680)))) + (e * (e * (e * 942900))))) + (e * (e * (e * (e * 1278840)))))) + (e * (e * (e * (e * (e * 1148340))))))) + (e * (e * (e * (e * (e * (e * 686160)))))))) + (e * (e * (e * (e * (e * (e * (e * 264210))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong2_part_1_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_0 c d e := by
  unfold strong2_part_1_0
  positivity

theorem strong2_part_1_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 0 = strong2_part_1_0 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_0 <;> ring

def strong2_part_1_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 5880800) + ((d * 28369540) + (e * 14477740)))) + ((d * ((d * 67145140) + (e * 68518980))) + (e * (e * 20787600))))) + ((d * ((d * ((d * 98888400) + (e * 151610760))) + (e * (e * 97440620)))) + (e * (e * (e * 22992480)))))) + ((d * ((d * ((d * ((d * 95947400) + (e * 196878480))) + (e * (e * 197019220)))) + (e * (e * (e * 96737140))))) + (e * (e * (e * (e * 18526400))))))) + ((d * ((d * ((d * ((d * ((d * 61035160) + (e * 157519840))) + (e * (e * 216099860)))) + (e * (e * (e * 163455980))))) + (e * (e * (e * (e * 63799060)))))) + (e * (e * (e * (e * (e * 10075040)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 24333120) + (e * 76046160))) + (e * (e * 133890300)))) + (e * (e * (e * 138215500))))) + (e * (e * (e * (e * 82381980)))))) + (e * (e * (e * (e * (e * 26369220))))))) + (e * (e * (e * (e * (e * (e * 3542760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 5459860) + (e * 20168940))) + (e * (e * 43993740)))) + (e * (e * (e * 58301820))))) + (e * (e * (e * (e * 47310220)))))) + (e * (e * (e * (e * (e * 23102820))))))) + (e * (e * (e * (e * (e * (e * 6293640)))))))) + (e * (e * (e * (e * (e * (e * (e * 741940)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 517180) + (e * 2226900))) + (e * (e * 5929020)))) + (e * (e * (e * 9770060))))) + (e * (e * (e * (e * 10183820)))))) + (e * (e * (e * (e * (e * 6779140))))))) + (e * (e * (e * (e * (e * (e * 2818280)))))))) + (e * (e * (e * (e * (e * (e * (e * 672200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 70680))))))))))

private theorem strong2_part_1_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_1 c d e := by
  unfold strong2_part_1_1
  positivity

theorem strong2_part_1_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 1 = strong2_part_1_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_1 <;> ring

def strong2_part_1_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 26633280) + ((d * 114949300) + (e * 59269620)))) + ((d * ((d * 239297110) + (e * 246690780))) + (e * (e * 77377710))))) + ((d * ((d * ((d * 301036640) + (e * 467105950))) + (e * (e * 306623800)))) + (e * (e * (e * 72991710)))))) + ((d * ((d * ((d * ((d * 238621930) + (e * 497463540))) + (e * (e * 503581990)))) + (e * (e * (e * 246763800))))) + (e * (e * (e * (e * 46707680))))))) + ((d * ((d * ((d * ((d * ((d * 115845940) + (e * 305462910))) + (e * (e * 420855060)))) + (e * (e * (e * 315130710))))) + (e * (e * (e * (e * 120840260)))))) + (e * (e * (e * (e * (e * 18666120)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 31270130) + (e * 100582720))) + (e * (e * 176871600)))) + (e * (e * (e * 179591040))))) + (e * (e * (e * (e * 104575810)))))) + (e * (e * (e * (e * (e * 32569260))))))) + (e * (e * (e * (e * (e * (e * 4238450))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3566220) + (e * 13686170))) + (e * (e * 29665380)))) + (e * (e * (e * 38440340))))) + (e * (e * (e * (e * 30309620)))))) + (e * (e * (e * (e * (e * 14324070))))))) + (e * (e * (e * (e * (e * (e * 3758060)))))))) + (e * (e * (e * (e * (e * (e * (e * 424350)))))))))

private theorem strong2_part_1_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_2 c d e := by
  unfold strong2_part_1_2
  positivity

theorem strong2_part_1_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 2 = strong2_part_1_2 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_2 <;> ring

def strong2_part_1_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 70178720) + ((d * 265136360) + (e * 137009940)))) + ((d * ((d * 471665220) + (e * 487411920))) + (e * (e * 156973620))))) + ((d * ((d * ((d * 486379820) + (e * 758239220))) + (e * (e * 505262780)))) + (e * (e * (e * 121044600)))))) + ((d * ((d * ((d * ((d * 295287680) + (e * 620987860))) + (e * (e * 632402280)))) + (e * (e * (e * 308804820))))) + (e * (e * (e * (e * 57782440))))))) + ((d * ((d * ((d * ((d * ((d * 97293000) + (e * 260119460))) + (e * (e * 358133500)))) + (e * (e * (e * 265218420))))) + (e * (e * (e * (e * 99949360)))))) + (e * (e * (e * (e * (e * 15115380)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 13344420) + (e * 43775880))) + (e * (e * 76536380)))) + (e * (e * (e * 76394500))))) + (e * (e * (e * (e * 43483700)))))) + (e * (e * (e * (e * (e * 13194120))))))) + (e * (e * (e * (e * (e * (e * 1666860))))))))

private theorem strong2_part_1_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_3 c d e := by
  unfold strong2_part_1_3
  positivity

theorem strong2_part_1_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 3 = strong2_part_1_3 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_3 <;> ring

def strong2_part_1_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 118962400) + ((d * 381881280) + (e * 196504620)))) + ((d * ((d * 556448550) + (e * 572987840))) + (e * (e * 188512200))))) + ((d * ((d * ((d * 440379780) + (e * 686014010))) + (e * (e * 461864100)))) + (e * (e * (e * 111192200)))))) + ((d * ((d * ((d * ((d * 181862720) + (e * 383795400))) + (e * (e * 391522540)))) + (e * (e * (e * 190318160))))) + (e * (e * (e * (e * 35219930))))))) + ((d * ((d * ((d * ((d * ((d * 30483720) + (e * 82174380))) + (e * (e * 112646420)))) + (e * (e * (e * 82452200))))) + (e * (e * (e * (e * 30554220)))))) + (e * (e * (e * (e * (e * 4528890)))))))

private theorem strong2_part_1_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_4 c d e := by
  unfold strong2_part_1_4
  positivity

theorem strong2_part_1_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 4 = strong2_part_1_4 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_4 <;> ring

def strong2_part_1_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 135190920) + ((d * 353142600) + (e * 180138020)))) + ((d * ((d * 393954640) + (e * 402499560))) + (e * (e * 134708280))))) + ((d * ((d * ((d * 212139580) + (e * 328895540))) + (e * (e * 222813060)))) + (e * (e * (e * 53844020)))))) + ((d * ((d * ((d * ((d * 44616900) + (e * 94126300))) + (e * (e * 95838220)))) + (e * (e * (e * 46328820))))) + (e * (e * (e * (e * 8480280))))))

private theorem strong2_part_1_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_5 c d e := by
  unfold strong2_part_1_5
  positivity

theorem strong2_part_1_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 5 = strong2_part_1_5 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_5 <;> ring

def strong2_part_1_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 103836250) + ((d * 206153500) + (e * 104049750)))) + ((d * ((d * 155676640) + (e * 157409140))) + (e * (e * 53359390))))) + ((d * ((d * ((d * 42589260) + (e * 65509640))) + (e * (e * 44460640)))) + (e * (e * (e * 10770130)))))

private theorem strong2_part_1_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_6 c d e := by
  unfold strong2_part_1_6
  positivity

theorem strong2_part_1_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 6 = strong2_part_1_6 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_6 <;> ring

def strong2_part_1_7 (c d e : ℝ) : ℝ :=
  ((c * ((c * 52678940) + ((d * 70258920) + (e * 35159960)))) + ((d * ((d * 26691000) + (e * 26691000))) + (e * (e * 9111020))))

private theorem strong2_part_1_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_7 c d e := by
  unfold strong2_part_1_7
  positivity

theorem strong2_part_1_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 7 = strong2_part_1_7 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_7 <;> ring

def strong2_part_1_8 (c d e : ℝ) : ℝ :=
  ((c * 16337970) + ((d * 10891980) + (e * 5445990)))

private theorem strong2_part_1_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_8 c d e := by
  unfold strong2_part_1_8
  positivity

theorem strong2_part_1_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 8 = strong2_part_1_8 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_8 <;> ring

def strong2_part_1_9 (c d e : ℝ) : ℝ :=
  2420440

private theorem strong2_part_1_9_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_1_9 c d e := by
  unfold strong2_part_1_9
  positivity

theorem strong2_part_1_9_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 1) 9 = strong2_part_1_9 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_1_9 <;> ring

theorem strong2_coeff_1_length (c d e : ℝ) :
    (chamberPoly2 c d e 1).length ≤ 10 := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong2_coeff_1_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly2 c d e 1) b := by
  apply polyEval_nonneg_of_coeff _ b 10
    (strong2_coeff_1_length c d e) hb
  apply forall_fin10
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 0
    rw [strong2_part_1_0_eq]
    exact strong2_part_1_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 1
    rw [strong2_part_1_1_eq]
    exact strong2_part_1_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 2
    rw [strong2_part_1_2_eq]
    exact strong2_part_1_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 3
    rw [strong2_part_1_3_eq]
    exact strong2_part_1_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 4
    rw [strong2_part_1_4_eq]
    exact strong2_part_1_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 5
    rw [strong2_part_1_5_eq]
    exact strong2_part_1_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 6
    rw [strong2_part_1_6_eq]
    exact strong2_part_1_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 7
    rw [strong2_part_1_7_eq]
    exact strong2_part_1_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 8
    rw [strong2_part_1_8_eq]
    exact strong2_part_1_8_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 1) 9
    rw [strong2_part_1_9_eq]
    exact strong2_part_1_9_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
