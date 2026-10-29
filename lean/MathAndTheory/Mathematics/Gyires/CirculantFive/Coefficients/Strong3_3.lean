module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a^3`

Generated certificate. The coefficient of `a^3` (a power of the smallest weight) in the chamber
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

def strong3_part_3_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 10965680) + ((d * 48585200) + (e * 24292600)))) + ((d * ((d * 104477360) + (e * 104477360))) + (e * (e * 33606520))))) + ((d * ((d * ((d * 135490400) + (e * 203235600))) + (e * (e * 134522640)))) + (e * (e * (e * 33388720)))))) + ((d * ((d * ((d * ((d * 110038800) + (e * 220077600))) + (e * (e * 220831440)))) + (e * (e * (e * 110792640))))) + (e * (e * (e * (e * 21695200))))))) + ((d * ((d * ((d * ((d * ((d * 54390320) + (e * 135975800))) + (e * (e * 182717040)))) + (e * (e * (e * 138099760))))) + (e * (e * (e * (e * 54127560)))))) + (e * (e * (e * (e * (e * 8579680)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 14877600) + (e * 44632800))) + (e * (e * 75358040)))) + (e * (e * (e * 76328080))))) + (e * (e * (e * (e * 44966280)))))) + (e * (e * (e * (e * (e * 14241040))))))) + (e * (e * (e * (e * (e * (e * 1887120))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1714640) + (e * 6001240))) + (e * (e * 12293320)))) + (e * (e * (e * 15730200))))) + (e * (e * (e * (e * 12435960)))))) + (e * (e * (e * (e * (e * 5924360))))))) + (e * (e * (e * (e * (e * (e * 1569640)))))))) + (e * (e * (e * (e * (e * (e * (e * 178880)))))))))

private theorem strong3_part_3_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_0 c d e := by
  unfold strong3_part_3_0
  positivity

theorem strong3_part_3_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 0 = strong3_part_3_0 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_0 <;> ring

def strong3_part_3_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 84353640) + ((d * 324177440) + (e * 161217200)))) + ((d * ((d * 593549000) + (e * 589930960))) + (e * (e * 195377080))))) + ((d * ((d * ((d * 630252800) + (e * 937014960))) + (e * (e * 630078640)))) + (e * (e * (e * 160794000)))))) + ((d * ((d * ((d * ((d * 391762800) + (e * 772914960))) + (e * (e * 777544400)))) + (e * (e * (e * 396121120))))) + (e * (e * (e * (e * 78764240))))))) + ((d * ((d * ((d * ((d * ((d * 131200960) + (e * 321488160))) + (e * (e * 427962160)))) + (e * (e * (e * 325208560))))) + (e * (e * (e * (e * 128569600)))))) + (e * (e * (e * (e * (e * 20518000)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 18170360) + (e * 52989760))) + (e * (e * 87667520)))) + (e * (e * (e * 88568320))))) + (e * (e * (e * (e * 52353560)))))) + (e * (e * (e * (e * (e * 16633360))))))) + (e * (e * (e * (e * (e * (e * 2204600))))))))

private theorem strong3_part_3_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_1 c d e := by
  unfold strong3_part_3_1
  positivity

theorem strong3_part_3_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 1 = strong3_part_3_1 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_1 <;> ring

def strong3_part_3_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 275630840) + ((d * 892973960) + (e * 443913080)))) + ((d * ((d * 1339192960) + (e * 1328430080))) + (e * (e * 454842560))))) + ((d * ((d * ((d * 1094582160) + (e * 1618616880))) + (e * (e * 1107877440)))) + (e * (e * (e * 290151600)))))) + ((d * ((d * ((d * ((d * 464109360) + (e * 906134880))) + (e * (e * 914330640)))) + (e * (e * (e * 472034000))))) + (e * (e * (e * (e * 94968320))))))) + ((d * ((d * ((d * ((d * ((d * 79175720) + (e * 190787280))) + (e * (e * 251488160)))) + (e * (e * (e * 191690000))))) + (e * (e * (e * (e * 76216040)))))) + (e * (e * (e * (e * (e * 12201320)))))))

private theorem strong3_part_3_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_2 c d e := by
  unfold strong3_part_3_2
  positivity

theorem strong3_part_3_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 2 = strong3_part_3_2 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_2 <;> ring

def strong3_part_3_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 498673000) + ((d * 1306674320) + (e * 651658240)))) + ((d * ((d * 1506511440) + (e * 1496132240))) + (e * (e * 530776400))))) + ((d * ((d * ((d * 843821360) + (e * 1244735600))) + (e * (e * 867685120)))) + (e * (e * (e * 232479920)))))) + ((d * ((d * ((d * ((d * 183308480) + (e * 355226320))) + (e * (e * 359362480)))) + (e * (e * (e * 187444640))))) + (e * (e * (e * (e * 37997240))))))

private theorem strong3_part_3_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_3 c d e := by
  unfold strong3_part_3_3
  positivity

theorem strong3_part_3_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 3 = strong3_part_3_3 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_3 <;> ring

def strong3_part_3_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 545456440) + ((d * 1082209720) + (e * 542222080)))) + ((d * ((d * 851429240) + (e * 848194880))) + (e * (e * 311441600))))) + ((d * ((d * ((d * 244844400) + (e * 361297840))) + (e * (e * 256116560)))) + (e * (e * (e * 69831560)))))

private theorem strong3_part_3_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_4 c d e := by
  unfold strong3_part_3_4
  positivity

theorem strong3_part_3_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 4 = strong3_part_3_4 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_4 <;> ring

def strong3_part_3_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * 368344600) + ((d * 490396960) + (e * 246292240)))) + ((d * ((d * 196052560) + (e * 196052560))) + (e * (e * 74000200))))

private theorem strong3_part_3_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_5 c d e := by
  unfold strong3_part_3_5
  positivity

theorem strong3_part_3_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 5 = strong3_part_3_5 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_5 <;> ring

def strong3_part_3_6 (c d e : ℝ) : ℝ :=
  ((c * 147172200) + ((d * 98114800) + (e * 49057400)))

private theorem strong3_part_3_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_6 c d e := by
  unfold strong3_part_3_6
  positivity

theorem strong3_part_3_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 6 = strong3_part_3_6 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_6 <;> ring

def strong3_part_3_7 (c d e : ℝ) : ℝ :=
  28032800

private theorem strong3_part_3_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_3_7 c d e := by
  unfold strong3_part_3_7
  positivity

theorem strong3_part_3_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 3) 7 = strong3_part_3_7 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_3_7 <;> ring

theorem strong3_coeff_3_length (c d e : ℝ) :
    (chamberPoly3 c d e 3).length ≤ 8 := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong3_coeff_3_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly3 c d e 3) b := by
  apply polyEval_nonneg_of_coeff _ b 8
    (strong3_coeff_3_length c d e) hb
  apply forall_fin8
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 0
    rw [strong3_part_3_0_eq]
    exact strong3_part_3_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 1
    rw [strong3_part_3_1_eq]
    exact strong3_part_3_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 2
    rw [strong3_part_3_2_eq]
    exact strong3_part_3_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 3
    rw [strong3_part_3_3_eq]
    exact strong3_part_3_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 4
    rw [strong3_part_3_4_eq]
    exact strong3_part_3_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 5
    rw [strong3_part_3_5_eq]
    exact strong3_part_3_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 6
    rw [strong3_part_3_6_eq]
    exact strong3_part_3_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 3) 7
    rw [strong3_part_3_7_eq]
    exact strong3_part_3_7_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
