module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a^3`

Generated certificate. The coefficient of `a^3` (a power of the smallest weight) in the chamber
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

def strong2_part_3_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 10965680) + ((d * 48585200) + (e * 24292600)))) + ((d * ((d * 104477360) + (e * 104477360))) + (e * (e * 33606520))))) + ((d * ((d * ((d * 135490400) + (e * 203235600))) + (e * (e * 134522640)))) + (e * (e * (e * 33388720)))))) + ((d * ((d * ((d * ((d * 110038800) + (e * 220077600))) + (e * (e * 220831440)))) + (e * (e * (e * 110792640))))) + (e * (e * (e * (e * 21695200))))))) + ((d * ((d * ((d * ((d * ((d * 54390320) + (e * 135975800))) + (e * (e * 182717040)))) + (e * (e * (e * 138099760))))) + (e * (e * (e * (e * 54127560)))))) + (e * (e * (e * (e * (e * 8579680)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 14877600) + (e * 44632800))) + (e * (e * 75358040)))) + (e * (e * (e * 76328080))))) + (e * (e * (e * (e * 44966280)))))) + (e * (e * (e * (e * (e * 14241040))))))) + (e * (e * (e * (e * (e * (e * 1887120))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1714640) + (e * 6001240))) + (e * (e * 12293320)))) + (e * (e * (e * 15730200))))) + (e * (e * (e * (e * 12435960)))))) + (e * (e * (e * (e * (e * 5924360))))))) + (e * (e * (e * (e * (e * (e * 1569640)))))))) + (e * (e * (e * (e * (e * (e * (e * 178880)))))))))

private theorem strong2_part_3_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_0 c d e := by
  unfold strong2_part_3_0
  positivity

theorem strong2_part_3_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 0 = strong2_part_3_0 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_0 <;> ring

def strong2_part_3_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 84353640) + ((d * 324177440) + (e * 162960240)))) + ((d * ((d * 593549000) + (e * 597167040))) + (e * (e * 198995120))))) + ((d * ((d * ((d * 630252800) + (e * 953743440))) + (e * (e * 646807120)))) + (e * (e * (e * 162522480)))))) + ((d * ((d * ((d * ((d * 391762800) + (e * 794136240))) + (e * (e * 809376320)))) + (e * (e * (e * 407274000))))) + (e * (e * (e * (e * 79035360))))))) + ((d * ((d * ((d * ((d * ((d * 131200960) + (e * 334516640))) + (e * (e * 454019120)))) + (e * (e * (e * 341758560))))) + (e * (e * (e * (e * 132091120)))))) + (e * (e * (e * (e * (e * 20518000)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 18170360) + (e * 56032400))) + (e * (e * 95274120)))) + (e * (e * (e * 95611360))))) + (e * (e * (e * (e * 55311520)))))) + (e * (e * (e * (e * (e * 17112240))))))) + (e * (e * (e * (e * (e * (e * 2204600))))))))

private theorem strong2_part_3_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_1 c d e := by
  unfold strong2_part_3_1
  positivity

theorem strong2_part_3_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 1 = strong2_part_3_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_1 <;> ring

def strong2_part_3_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 275630840) + ((d * 892973960) + (e * 449060880)))) + ((d * ((d * 1339192960) + (e * 1349955840))) + (e * (e * 465605440))))) + ((d * ((d * ((d * 1094582160) + (e * 1665129600))) + (e * (e * 1154390160)))) + (e * (e * (e * 293691120)))))) + ((d * ((d * ((d * ((d * 464109360) + (e * 950302560))) + (e * (e * 980582160)))) + (e * (e * (e * 494660080))))) + (e * (e * (e * (e * 95239440))))))) + ((d * ((d * ((d * ((d * ((d * 79175720) + (e * 205091320))) + (e * (e * 280096240)))) + (e * (e * (e * 209808000))))) + (e * (e * (e * (e * 80030000)))))) + (e * (e * (e * (e * (e * 12201320)))))))

private theorem strong2_part_3_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_2 c d e := by
  unfold strong2_part_3_2
  positivity

theorem strong2_part_3_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 2 = strong2_part_3_2 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_2 <;> ring

def strong2_part_3_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 498673000) + ((d * 1306674320) + (e * 655016080)))) + ((d * ((d * 1506511440) + (e * 1516890640))) + (e * (e * 541155600))))) + ((d * ((d * ((d * 843821360) + (e * 1286728480))) + (e * (e * 909678000)))) + (e * (e * (e * 234290960)))))) + ((d * ((d * ((d * ((d * 183308480) + (e * 378007600))) + (e * (e * 393534400)))) + (e * (e * (e * 198835280))))) + (e * (e * (e * (e * 37997240))))))

private theorem strong2_part_3_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_3 c d e := by
  unfold strong2_part_3_3
  positivity

theorem strong2_part_3_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 3 = strong2_part_3_3 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_3 <;> ring

def strong2_part_3_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 545456440) + ((d * 1082209720) + (e * 539987640)))) + ((d * ((d * 851429240) + (e * 854663600))) + (e * (e * 314675960))))) + ((d * ((d * ((d * 244844400) + (e * 373235360))) + (e * (e * 268054080)))) + (e * (e * (e * 69831560)))))

private theorem strong2_part_3_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_4 c d e := by
  unfold strong2_part_3_4
  positivity

theorem strong2_part_3_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 4 = strong2_part_3_4 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_4 <;> ring

def strong2_part_3_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * 368344600) + ((d * 490396960) + (e * 244104720)))) + ((d * ((d * 196052560) + (e * 196052560))) + (e * (e * 74000200))))

private theorem strong2_part_3_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_5 c d e := by
  unfold strong2_part_3_5
  positivity

theorem strong2_part_3_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 5 = strong2_part_3_5 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_5 <;> ring

def strong2_part_3_6 (c d e : ℝ) : ℝ :=
  ((c * 147172200) + ((d * 98114800) + (e * 49057400)))

private theorem strong2_part_3_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_6 c d e := by
  unfold strong2_part_3_6
  positivity

theorem strong2_part_3_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 6 = strong2_part_3_6 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_6 <;> ring

def strong2_part_3_7 (c d e : ℝ) : ℝ :=
  28032800

private theorem strong2_part_3_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_3_7 c d e := by
  unfold strong2_part_3_7
  positivity

theorem strong2_part_3_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 3) 7 = strong2_part_3_7 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_3_7 <;> ring

theorem strong2_coeff_3_length (c d e : ℝ) :
    (chamberPoly2 c d e 3).length ≤ 8 := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong2_coeff_3_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly2 c d e 3) b := by
  apply polyEval_nonneg_of_coeff _ b 8
    (strong2_coeff_3_length c d e) hb
  apply forall_fin8
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 0
    rw [strong2_part_3_0_eq]
    exact strong2_part_3_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 1
    rw [strong2_part_3_1_eq]
    exact strong2_part_3_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 2
    rw [strong2_part_3_2_eq]
    exact strong2_part_3_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 3
    rw [strong2_part_3_3_eq]
    exact strong2_part_3_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 4
    rw [strong2_part_3_4_eq]
    exact strong2_part_3_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 5
    rw [strong2_part_3_5_eq]
    exact strong2_part_3_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 6
    rw [strong2_part_3_6_eq]
    exact strong2_part_3_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 3) 7
    rw [strong2_part_3_7_eq]
    exact strong2_part_3_7_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
