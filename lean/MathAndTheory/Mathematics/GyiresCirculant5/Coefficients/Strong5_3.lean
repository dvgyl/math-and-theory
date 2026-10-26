module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a^3`

Generated certificate. The coefficient of `a^3` (a power of the smallest weight) in the chamber
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

def strong5_part_3_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 10965680) + ((d * 52467160) + (e * 24292600)))) + ((d * ((d * 118130200) + (e * 108491280))) + (e * (e * 33606520))))) + ((d * ((d * ((d * 154053680) + (e * 212423880))) + (e * (e * 133676120)))) + (e * (e * (e * 33388720)))))) + ((d * ((d * ((d * ((d * 122152320) + (e * 226622880))) + (e * (e * 217264000)))) + (e * (e * (e * 109543040))))) + (e * (e * (e * (e * 21695200))))))) + ((d * ((d * ((d * ((d * ((d * 58129080) + (e * 137078320))) + (e * (e * 178414160)))) + (e * (e * (e * 135683120))))) + (e * (e * (e * (e * 53856440)))))) + (e * (e * (e * (e * (e * 8579680)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 15295240) + (e * 44364400))) + (e * (e * 73776080)))) + (e * (e * (e * 75161040))))) + (e * (e * (e * (e * 44695160)))))) + (e * (e * (e * (e * (e * 14241040))))))) + (e * (e * (e * (e * (e * (e * 1887120))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1714640) + (e * 6001240))) + (e * (e * 12293320)))) + (e * (e * (e * 15730200))))) + (e * (e * (e * (e * 12435960)))))) + (e * (e * (e * (e * (e * 5924360))))))) + (e * (e * (e * (e * (e * (e * 1569640)))))))) + (e * (e * (e * (e * (e * (e * (e * 178880)))))))))

private theorem strong5_part_3_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_0 c d e := by
  unfold strong5_part_3_0
  positivity

theorem strong5_part_3_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 0 = strong5_part_3_0 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_0 <;> ring

def strong5_part_3_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 84353640) + ((d * 343161600) + (e * 161217200)))) + ((d * ((d * 649498520) + (e * 606909200))) + (e * (e * 195377080))))) + ((d * ((d * ((d * 690928400) + (e * 974704480))) + (e * (e * 633811680)))) + (e * (e * (e * 160794000)))))) + ((d * ((d * ((d * ((d * 421140840) + (e * 803697680))) + (e * (e * 790939040)))) + (e * (e * (e * 401317840))))) + (e * (e * (e * (e * 78764240))))))) + ((d * ((d * ((d * ((d * ((d * 137286400) + (e * 334333840))) + (e * (e * 443377280)))) + (e * (e * (e * 336363840))))) + (e * (e * (e * (e * 131548880)))))) + (e * (e * (e * (e * (e * 20518000)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 18588000) + (e * 55764000))) + (e * (e * 93692160)))) + (e * (e * (e * 94444320))))) + (e * (e * (e * (e * 55040400)))))) + (e * (e * (e * (e * (e * 17112240))))))) + (e * (e * (e * (e * (e * (e * 2204600))))))))

private theorem strong5_part_3_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_1 c d e := by
  unfold strong5_part_3_1
  positivity

theorem strong5_part_3_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 1 = strong5_part_3_1 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_1 <;> ring

def strong5_part_3_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 275630840) + ((d * 929093320) + (e * 443913080)))) + ((d * ((d * 1425670320) + (e * 1356907360))) + (e * (e * 454842560))))) + ((d * ((d * ((d * 1165068320) + (e * 1680560400))) + (e * (e * 1127105040)))) + (e * (e * (e * 290151600)))))) + ((d * ((d * ((d * ((d * 486584200) + (e * 952348720))) + (e * (e * 957720960)))) + (e * (e * (e * 488142480))))) + (e * (e * (e * (e * 94968320))))))) + ((d * ((d * ((d * ((d * ((d * 81522400) + (e * 203806000))) + (e * (e * 273757280)))) + (e * (e * (e * 206829920))))) + (e * (e * (e * (e * 79758880)))))) + (e * (e * (e * (e * (e * 12201320)))))))

private theorem strong5_part_3_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_2 c d e := by
  unfold strong5_part_3_2
  positivity

theorem strong5_part_3_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 2 = strong5_part_3_2 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_2 <;> ring

def strong5_part_3_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 498673000) + ((d * 1339675920) + (e * 651658240)))) + ((d * ((d * 1568145360) + (e * 1520395280))) + (e * (e * 530776400))))) + ((d * ((d * ((d * 877664000) + (e * 1292620960))) + (e * (e * 891307440)))) + (e * (e * (e * 232479920)))))) + ((d * ((d * ((d * ((d * 188518800) + (e * 377037600))) + (e * (e * 385543040)))) + (e * (e * (e * 197024240))))) + (e * (e * (e * (e * 37997240))))))

private theorem strong5_part_3_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_3 c d e := by
  unfold strong5_part_3_3
  positivity

theorem strong5_part_3_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 3 = strong5_part_3_3 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_3 <;> ring

def strong5_part_3_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 545456440) + ((d * 1096381680) + (e * 542222080)))) + ((d * ((d * 871070000) + (e * 859132480))) + (e * (e * 311441600))))) + ((d * ((d * ((d * 250313200) + (e * 375469800))) + (e * (e * 264819720)))) + (e * (e * (e * 69831560)))))

private theorem strong5_part_3_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_4 c d e := by
  unfold strong5_part_3_4
  positivity

theorem strong5_part_3_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 4 = strong5_part_3_4 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_4 <;> ring

def strong5_part_3_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * 368344600) + ((d * 492584480) + (e * 246292240)))) + ((d * ((d * 198240080) + (e * 198240080))) + (e * (e * 74000200))))

private theorem strong5_part_3_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_5 c d e := by
  unfold strong5_part_3_5
  positivity

theorem strong5_part_3_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 5 = strong5_part_3_5 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_5 <;> ring

def strong5_part_3_6 (c d e : ℝ) : ℝ :=
  ((c * 147172200) + ((d * 98114800) + (e * 49057400)))

private theorem strong5_part_3_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_6 c d e := by
  unfold strong5_part_3_6
  positivity

theorem strong5_part_3_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 6 = strong5_part_3_6 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_6 <;> ring

def strong5_part_3_7 (c d e : ℝ) : ℝ :=
  28032800

private theorem strong5_part_3_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_3_7 c d e := by
  unfold strong5_part_3_7
  positivity

theorem strong5_part_3_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 3) 7 = strong5_part_3_7 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_3_7 <;> ring

theorem strong5_coeff_3_length (c d e : ℝ) :
    (chamberPoly5 c d e 3).length ≤ 8 := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong5_coeff_3_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly5 c d e 3) b := by
  apply polyEval_nonneg_of_coeff _ b 8
    (strong5_coeff_3_length c d e) hb
  apply forall_fin8
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 0
    rw [strong5_part_3_0_eq]
    exact strong5_part_3_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 1
    rw [strong5_part_3_1_eq]
    exact strong5_part_3_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 2
    rw [strong5_part_3_2_eq]
    exact strong5_part_3_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 3
    rw [strong5_part_3_3_eq]
    exact strong5_part_3_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 4
    rw [strong5_part_3_4_eq]
    exact strong5_part_3_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 5
    rw [strong5_part_3_5_eq]
    exact strong5_part_3_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 6
    rw [strong5_part_3_6_eq]
    exact strong5_part_3_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 3) 7
    rw [strong5_part_3_7_eq]
    exact strong5_part_3_7_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
