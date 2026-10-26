module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a^3`

Generated certificate. The coefficient of `a^3` (a power of the smallest weight) in the chamber
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

def strong0_part_3_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 10965680) + ((d * 52467160) + (e * 24292600)))) + ((d * ((d * 118130200) + (e * 108491280))) + (e * (e * 33606520))))) + ((d * ((d * ((d * 154053680) + (e * 212423880))) + (e * (e * 133676120)))) + (e * (e * (e * 33388720)))))) + ((d * ((d * ((d * ((d * 122152320) + (e * 226622880))) + (e * (e * 217264000)))) + (e * (e * (e * 109543040))))) + (e * (e * (e * (e * 21695200))))))) + ((d * ((d * ((d * ((d * ((d * 58129080) + (e * 137078320))) + (e * (e * 178414160)))) + (e * (e * (e * 135683120))))) + (e * (e * (e * (e * 53856440)))))) + (e * (e * (e * (e * (e * 8579680)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 15295240) + (e * 44364400))) + (e * (e * 73776080)))) + (e * (e * (e * 75161040))))) + (e * (e * (e * (e * 44695160)))))) + (e * (e * (e * (e * (e * 14241040))))))) + (e * (e * (e * (e * (e * (e * 1887120))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1714640) + (e * 6001240))) + (e * (e * 12293320)))) + (e * (e * (e * 15730200))))) + (e * (e * (e * (e * 12435960)))))) + (e * (e * (e * (e * (e * 5924360))))))) + (e * (e * (e * (e * (e * (e * 1569640)))))))) + (e * (e * (e * (e * (e * (e * (e * 178880)))))))))

private theorem strong0_part_3_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_0 c d e := by
  unfold strong0_part_3_0
  positivity

theorem strong0_part_3_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 0 = strong0_part_3_0 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_0 <;> ring

def strong0_part_3_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 84353640) + ((d * 344904640) + (e * 162960240)))) + ((d * ((d * 654595680) + (e * 615624400))) + (e * (e * 198995120))))) + ((d * ((d * ((d * 695615120) + (e * 980591840))) + (e * (e * 636740800)))) + (e * (e * (e * 162522480)))))) + ((d * ((d * ((d * ((d * 421777320) + (e * 796567360))) + (e * (e * 778018160)))) + (e * (e * (e * 396434880))))) + (e * (e * (e * (e * 79035360))))))) + ((d * ((d * ((d * ((d * ((d * 136172640) + (e * 325035200))) + (e * (e * 425684240)))) + (e * (e * (e * 323876400))))) + (e * (e * (e * (e * 128569600)))))) + (e * (e * (e * (e * (e * 20518000)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 18170360) + (e * 52989760))) + (e * (e * 87667520)))) + (e * (e * (e * 88568320))))) + (e * (e * (e * (e * 52353560)))))) + (e * (e * (e * (e * (e * 16633360))))))) + (e * (e * (e * (e * (e * (e * 2204600))))))))

private theorem strong0_part_3_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_1 c d e := by
  unfold strong0_part_3_1
  positivity

theorem strong0_part_3_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 1 = strong0_part_3_1 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_1 <;> ring

def strong0_part_3_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 275630840) + ((d * 934241120) + (e * 449060880)))) + ((d * ((d * 1435498640) + (e * 1377498560))) + (e * (e * 465605440))))) + ((d * ((d * ((d * 1167206000) + (e * 1675553040))) + (e * (e * 1123499520)))) + (e * (e * (e * 293691120)))))) + ((d * ((d * ((d * ((d * 481694680) + (e * 922693200))) + (e * (e * 918221280)))) + (e * (e * (e * 473679920))))) + (e * (e * (e * (e * 95239440))))))) + ((d * ((d * ((d * ((d * ((d * 79175720) + (e * 190787280))) + (e * (e * 251488160)))) + (e * (e * (e * 191690000))))) + (e * (e * (e * (e * 76216040)))))) + (e * (e * (e * (e * (e * 12201320)))))))

private theorem strong0_part_3_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_2 c d e := by
  unfold strong0_part_3_2
  positivity

theorem strong0_part_3_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 2 = strong0_part_3_2 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_2 <;> ring

def strong0_part_3_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 498673000) + ((d * 1343033760) + (e * 655016080)))) + ((d * ((d * 1567839680) + (e * 1530468800))) + (e * (e * 541155600))))) + ((d * ((d * ((d * 868790160) + (e * 1266134720))) + (e * (e * 875506080)))) + (e * (e * (e * 234290960)))))) + ((d * ((d * ((d * ((d * 183308480) + (e * 355226320))) + (e * (e * 359362480)))) + (e * (e * (e * 187444640))))) + (e * (e * (e * (e * 37997240))))))

private theorem strong0_part_3_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_3 c d e := by
  unfold strong0_part_3_3
  positivity

theorem strong0_part_3_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 3 = strong0_part_3_3 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_3 <;> ring

def strong0_part_3_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 545456440) + ((d * 1094147240) + (e * 539987640)))) + ((d * ((d * 863366760) + (e * 854663600))) + (e * (e * 314675960))))) + ((d * ((d * ((d * 244844400) + (e * 361297840))) + (e * (e * 256116560)))) + (e * (e * (e * 69831560)))))

private theorem strong0_part_3_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_4 c d e := by
  unfold strong0_part_3_4
  positivity

theorem strong0_part_3_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 4 = strong0_part_3_4 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_4 <;> ring

def strong0_part_3_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * 368344600) + ((d * 490396960) + (e * 244104720)))) + ((d * ((d * 196052560) + (e * 196052560))) + (e * (e * 74000200))))

private theorem strong0_part_3_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_5 c d e := by
  unfold strong0_part_3_5
  positivity

theorem strong0_part_3_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 5 = strong0_part_3_5 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_5 <;> ring

def strong0_part_3_6 (c d e : ℝ) : ℝ :=
  ((c * 147172200) + ((d * 98114800) + (e * 49057400)))

private theorem strong0_part_3_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_6 c d e := by
  unfold strong0_part_3_6
  positivity

theorem strong0_part_3_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 6 = strong0_part_3_6 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_6 <;> ring

def strong0_part_3_7 (c d e : ℝ) : ℝ :=
  28032800

private theorem strong0_part_3_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_3_7 c d e := by
  unfold strong0_part_3_7
  positivity

theorem strong0_part_3_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 3) 7 = strong0_part_3_7 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong0_part_3_7 <;> ring

theorem strong0_coeff_3_length (c d e : ℝ) :
    (chamberPoly0 c d e 3).length ≤ 8 := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong0_coeff_3_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly0 c d e 3) b := by
  apply polyEval_nonneg_of_coeff _ b 8
    (strong0_coeff_3_length c d e) hb
  apply forall_fin8
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 0
    rw [strong0_part_3_0_eq]
    exact strong0_part_3_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 1
    rw [strong0_part_3_1_eq]
    exact strong0_part_3_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 2
    rw [strong0_part_3_2_eq]
    exact strong0_part_3_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 3
    rw [strong0_part_3_3_eq]
    exact strong0_part_3_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 4
    rw [strong0_part_3_4_eq]
    exact strong0_part_3_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 5
    rw [strong0_part_3_5_eq]
    exact strong0_part_3_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 6
    rw [strong0_part_3_6_eq]
    exact strong0_part_3_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 3) 7
    rw [strong0_part_3_7_eq]
    exact strong0_part_3_7_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
