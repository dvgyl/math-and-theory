module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a^3`

Generated certificate. The coefficient of `a^3` (a power of the smallest weight) in the chamber
polynomial `chamberPoly4` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong4_part_3_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 10965680) + ((d * 52467160) + (e * 28174560)))) + ((d * ((d * 118130200) + (e * 127769120))) + (e * (e * 43245440))))) + ((d * ((d * ((d * 154053680) + (e * 249737160))) + (e * (e * 170989400)))) + (e * (e * (e * 41917200)))))) + ((d * ((d * ((d * ((d * 122152320) + (e * 261986400))) + (e * (e * 270309280)))) + (e * (e * (e * 133725600))))) + (e * (e * (e * (e * 24945600))))))) + ((d * ((d * ((d * ((d * ((d * 58129080) + (e * 153567080))) + (e * (e * 211391680)))) + (e * (e * (e * 158380240))))) + (e * (e * (e * (e * 60064800)))))) + (e * (e * (e * (e * (e * 9058560)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 15295240) + (e * 47407040))) + (e * (e * 81382680)))) + (e * (e * (e * 82204080))))) + (e * (e * (e * (e * 47653120)))))) + (e * (e * (e * (e * (e * 14719920))))))) + (e * (e * (e * (e * (e * (e * 1887120))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1714640) + (e * 6001240))) + (e * (e * 12293320)))) + (e * (e * (e * 15730200))))) + (e * (e * (e * (e * 12435960)))))) + (e * (e * (e * (e * (e * 5924360))))))) + (e * (e * (e * (e * (e * (e * 1569640)))))))) + (e * (e * (e * (e * (e * (e * (e * 178880)))))))))

private theorem strong4_part_3_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_0 c d e := by
  unfold strong4_part_3_0
  positivity

theorem strong4_part_3_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 0 = strong4_part_3_0 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_0 <;> ring

def strong4_part_3_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 84353640) + ((d * 343161600) + (e * 181944400)))) + ((d * ((d * 649498520) + (e * 692087840))) + (e * (e * 237966400))))) + ((d * ((d * ((d * 690928400) + (e * 1098080720))) + (e * (e * 757187920)))) + (e * (e * (e * 189241600)))))) + ((d * ((d * ((d * ((d * 421140840) + (e * 880865680))) + (e * (e * 906691040)))) + (e * (e * (e * 454030560))))) + (e * (e * (e * (e * 85828600))))))) + ((d * ((d * ((d * ((d * ((d * 137286400) + (e * 352098160))) + (e * (e * 478905920)))) + (e * (e * (e * 360628960))))) + (e * (e * (e * (e * 138049680)))))) + (e * (e * (e * (e * (e * 20996880)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 18588000) + (e * 55764000))) + (e * (e * 93692160)))) + (e * (e * (e * 94444320))))) + (e * (e * (e * (e * 55040400)))))) + (e * (e * (e * (e * (e * 17112240))))))) + (e * (e * (e * (e * (e * (e * 2204600))))))))

private theorem strong4_part_3_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_1 c d e := by
  unfold strong4_part_3_1
  positivity

theorem strong4_part_3_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 1 = strong4_part_3_1 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_1 <;> ring

def strong4_part_3_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 275630840) + ((d * 929093320) + (e * 485180240)))) + ((d * ((d * 1425670320) + (e * 1494433280))) + (e * (e * 523605520))))) + ((d * ((d * ((d * 1165068320) + (e * 1814644560))) + (e * (e * 1261189200)))) + (e * (e * (e * 321461360)))))) + ((d * ((d * ((d * ((d * 486584200) + (e * 993988080))) + (e * (e * 1020180000)))) + (e * (e * (e * 516590080))))) + (e * (e * (e * (e * 98782280))))))) + ((d * ((d * ((d * ((d * ((d * 81522400) + (e * 203806000))) + (e * (e * 273757280)))) + (e * (e * (e * 206829920))))) + (e * (e * (e * (e * 79758880)))))) + (e * (e * (e * (e * (e * 12201320)))))))

private theorem strong4_part_3_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_2 c d e := by
  unfold strong4_part_3_2
  positivity

theorem strong4_part_3_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 2 = strong4_part_3_2 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_2 <;> ring

def strong4_part_3_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 498673000) + ((d * 1339675920) + (e * 688017680)))) + ((d * ((d * 1568145360) + (e * 1615895440))) + (e * (e * 578526480))))) + ((d * ((d * ((d * 877664000) + (e * 1340371040))) + (e * (e * 939057520)))) + (e * (e * (e * 243870560)))))) + ((d * ((d * ((d * ((d * 188518800) + (e * 377037600))) + (e * (e * 385543040)))) + (e * (e * (e * 197024240))))) + (e * (e * (e * (e * 37997240))))))

private theorem strong4_part_3_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_3 c d e := by
  unfold strong4_part_3_3
  positivity

theorem strong4_part_3_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 3 = strong4_part_3_3 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_3 <;> ring

def strong4_part_3_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 545456440) + ((d * 1096381680) + (e * 554159600)))) + ((d * ((d * 871070000) + (e * 883007520))) + (e * (e * 323379120))))) + ((d * ((d * ((d * 250313200) + (e * 375469800))) + (e * (e * 264819720)))) + (e * (e * (e * 69831560)))))

private theorem strong4_part_3_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_4 c d e := by
  unfold strong4_part_3_4
  positivity

theorem strong4_part_3_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 4 = strong4_part_3_4 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_4 <;> ring

def strong4_part_3_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * 368344600) + ((d * 492584480) + (e * 246292240)))) + ((d * ((d * 198240080) + (e * 198240080))) + (e * (e * 74000200))))

private theorem strong4_part_3_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_5 c d e := by
  unfold strong4_part_3_5
  positivity

theorem strong4_part_3_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 5 = strong4_part_3_5 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_5 <;> ring

def strong4_part_3_6 (c d e : ℝ) : ℝ :=
  ((c * 147172200) + ((d * 98114800) + (e * 49057400)))

private theorem strong4_part_3_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_6 c d e := by
  unfold strong4_part_3_6
  positivity

theorem strong4_part_3_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 6 = strong4_part_3_6 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_6 <;> ring

def strong4_part_3_7 (c d e : ℝ) : ℝ :=
  28032800

private theorem strong4_part_3_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_3_7 c d e := by
  unfold strong4_part_3_7
  positivity

theorem strong4_part_3_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 3) 7 = strong4_part_3_7 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_3_7 <;> ring

theorem strong4_coeff_3_length (c d e : ℝ) :
    (chamberPoly4 c d e 3).length ≤ 8 := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (3 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart3, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num

theorem strong4_coeff_3_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly4 c d e 3) b := by
  apply polyEval_nonneg_of_coeff _ b 8
    (strong4_coeff_3_length c d e) hb
  apply forall_fin8
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 0
    rw [strong4_part_3_0_eq]
    exact strong4_part_3_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 1
    rw [strong4_part_3_1_eq]
    exact strong4_part_3_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 2
    rw [strong4_part_3_2_eq]
    exact strong4_part_3_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 3
    rw [strong4_part_3_3_eq]
    exact strong4_part_3_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 4
    rw [strong4_part_3_4_eq]
    exact strong4_part_3_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 5
    rw [strong4_part_3_5_eq]
    exact strong4_part_3_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 6
    rw [strong4_part_3_6_eq]
    exact strong4_part_3_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 3) 7
    rw [strong4_part_3_7_eq]
    exact strong4_part_3_7_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
