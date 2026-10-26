module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a^3`

Generated certificate. The coefficient of `a^3` (a power of the smallest weight) in the chamber
polynomial `chamberPoly1` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong1_part_3_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 10965680) + ((d * 52467160) + (e * 28174560)))) + ((d * ((d * 118130200) + (e * 127769120))) + (e * (e * 43245440))))) + ((d * ((d * ((d * 154053680) + (e * 249737160))) + (e * (e * 170989400)))) + (e * (e * (e * 41917200)))))) + ((d * ((d * ((d * ((d * 122152320) + (e * 261986400))) + (e * (e * 270309280)))) + (e * (e * (e * 133725600))))) + (e * (e * (e * (e * 24945600))))))) + ((d * ((d * ((d * ((d * ((d * 58129080) + (e * 153567080))) + (e * (e * 211391680)))) + (e * (e * (e * 158380240))))) + (e * (e * (e * (e * 60064800)))))) + (e * (e * (e * (e * (e * 9058560)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 15295240) + (e * 47407040))) + (e * (e * 81382680)))) + (e * (e * (e * 82204080))))) + (e * (e * (e * (e * 47653120)))))) + (e * (e * (e * (e * (e * 14719920))))))) + (e * (e * (e * (e * (e * (e * 1887120))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1714640) + (e * 6001240))) + (e * (e * 12293320)))) + (e * (e * (e * 15730200))))) + (e * (e * (e * (e * 12435960)))))) + (e * (e * (e * (e * (e * 5924360))))))) + (e * (e * (e * (e * (e * (e * 1569640)))))))) + (e * (e * (e * (e * (e * (e * (e * 178880)))))))))

private theorem strong1_part_3_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_0 c d e := by
  unfold strong1_part_3_0
  positivity

theorem strong1_part_3_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 0 = strong1_part_3_0 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_0 <;> ring

def strong1_part_3_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 84353640) + ((d * 344904640) + (e * 181944400)))) + ((d * ((d * 654595680) + (e * 693566960))) + (e * (e * 237966400))))) + ((d * ((d * ((d * 695615120) + (e * 1106253520))) + (e * (e * 762402480)))) + (e * (e * (e * 189241600)))))) + ((d * ((d * ((d * ((d * 421777320) + (e * 890541920))) + (e * (e * 918980000)))) + (e * (e * (e * 457008640))))) + (e * (e * (e * (e * 85828600))))))) + ((d * ((d * ((d * ((d * ((d * 136172640) + (e * 355828000))) + (e * (e * 487269840)))) + (e * (e * (e * 364691520))))) + (e * (e * (e * (e * 138591920)))))) + (e * (e * (e * (e * (e * 20996880)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 18170360) + (e * 56032400))) + (e * (e * 95274120)))) + (e * (e * (e * 95611360))))) + (e * (e * (e * (e * 55311520)))))) + (e * (e * (e * (e * (e * 17112240))))))) + (e * (e * (e * (e * (e * (e * 2204600))))))))

private theorem strong1_part_3_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_1 c d e := by
  unfold strong1_part_3_1
  positivity

theorem strong1_part_3_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 1 = strong1_part_3_1 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_1 <;> ring

def strong1_part_3_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 275630840) + ((d * 934241120) + (e * 485180240)))) + ((d * ((d * 1435498640) + (e * 1493498720))) + (e * (e * 523605520))))) + ((d * ((d * ((d * 1167206000) + (e * 1826064960))) + (e * (e * 1274011440)))) + (e * (e * (e * 321461360)))))) + ((d * ((d * ((d * ((d * 481694680) + (e * 1004085520))) + (e * (e * 1040309760)))) + (e * (e * (e * 521461760))))) + (e * (e * (e * (e * 98782280))))))) + ((d * ((d * ((d * ((d * ((d * 79175720) + (e * 205091320))) + (e * (e * 280096240)))) + (e * (e * (e * 209808000))))) + (e * (e * (e * (e * 80030000)))))) + (e * (e * (e * (e * (e * 12201320)))))))

private theorem strong1_part_3_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_2 c d e := by
  unfold strong1_part_3_2
  positivity

theorem strong1_part_3_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 2 = strong1_part_3_2 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_2 <;> ring

def strong1_part_3_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 498673000) + ((d * 1343033760) + (e * 688017680)))) + ((d * ((d * 1567839680) + (e * 1605210560))) + (e * (e * 578526480))))) + ((d * ((d * ((d * 868790160) + (e * 1340235760))) + (e * (e * 949607120)))) + (e * (e * (e * 243870560)))))) + ((d * ((d * ((d * ((d * 183308480) + (e * 378007600))) + (e * (e * 393534400)))) + (e * (e * (e * 198835280))))) + (e * (e * (e * (e * 37997240))))))

private theorem strong1_part_3_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_3 c d e := by
  unfold strong1_part_3_3
  positivity

theorem strong1_part_3_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 3 = strong1_part_3_3 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_3 <;> ring

def strong1_part_3_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 545456440) + ((d * 1094147240) + (e * 554159600)))) + ((d * ((d * 863366760) + (e * 872069920))) + (e * (e * 323379120))))) + ((d * ((d * ((d * 244844400) + (e * 373235360))) + (e * (e * 268054080)))) + (e * (e * (e * 69831560)))))

private theorem strong1_part_3_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_4 c d e := by
  unfold strong1_part_3_4
  positivity

theorem strong1_part_3_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 4 = strong1_part_3_4 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_4 <;> ring

def strong1_part_3_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * 368344600) + ((d * 490396960) + (e * 246292240)))) + ((d * ((d * 196052560) + (e * 196052560))) + (e * (e * 74000200))))

private theorem strong1_part_3_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_5 c d e := by
  unfold strong1_part_3_5
  positivity

theorem strong1_part_3_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 5 = strong1_part_3_5 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_5 <;> ring

def strong1_part_3_6 (c d e : ℝ) : ℝ :=
  ((c * 147172200) + ((d * 98114800) + (e * 49057400)))

private theorem strong1_part_3_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_6 c d e := by
  unfold strong1_part_3_6
  positivity

theorem strong1_part_3_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 6 = strong1_part_3_6 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_6 <;> ring

def strong1_part_3_7 (c d e : ℝ) : ℝ :=
  28032800

private theorem strong1_part_3_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_3_7 c d e := by
  unfold strong1_part_3_7
  positivity

theorem strong1_part_3_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 3) 7 = strong1_part_3_7 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_3_7 <;> ring

theorem strong1_coeff_3_length (c d e : ℝ) :
    (chamberPoly1 c d e 3).length ≤ 8 := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num

theorem strong1_coeff_3_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly1 c d e 3) b := by
  apply polyEval_nonneg_of_coeff _ b 8
    (strong1_coeff_3_length c d e) hb
  apply forall_fin8
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 0
    rw [strong1_part_3_0_eq]
    exact strong1_part_3_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 1
    rw [strong1_part_3_1_eq]
    exact strong1_part_3_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 2
    rw [strong1_part_3_2_eq]
    exact strong1_part_3_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 3
    rw [strong1_part_3_3_eq]
    exact strong1_part_3_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 4
    rw [strong1_part_3_4_eq]
    exact strong1_part_3_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 5
    rw [strong1_part_3_5_eq]
    exact strong1_part_3_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 6
    rw [strong1_part_3_6_eq]
    exact strong1_part_3_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 3) 7
    rw [strong1_part_3_7_eq]
    exact strong1_part_3_7_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
