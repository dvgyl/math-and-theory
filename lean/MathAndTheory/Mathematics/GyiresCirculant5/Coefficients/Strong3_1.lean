module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a^1`

Generated certificate. The coefficient of `a^1` (a power of the smallest weight) in the chamber
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

def strong3_part_1_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 573910) + ((d * 3042420) + (e * 1521210)))) + ((d * ((d * 8017340) + (e * 8017340))) + (e * (e * 2327610))))) + ((d * ((d * ((d * 13443040) + (e * 20164560))) + (e * (e * 12578060)))) + (e * (e * (e * 2928270)))))) + ((d * ((d * ((d * ((d * 15339290) + (e * 30678580))) + (e * (e * 30120810)))) + (e * (e * (e * 14781520))))) + (e * (e * (e * (e * 2863180))))))) + ((d * ((d * ((d * ((d * ((d * 12003620) + (e * 30009050))) + (e * (e * 40720200)))) + (e * (e * (e * 31071250))))) + (e * (e * (e * (e * 12343960)))))) + (e * (e * (e * (e * (e * 1993740)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 6295220) + (e * 18885660))) + (e * (e * 33093610)))) + (e * (e * (e * 34711120))))) + (e * (e * (e * (e * 21182710)))))) + (e * (e * (e * (e * (e * 6974760))))))) + (e * (e * (e * (e * (e * (e * 969960))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2090160) + (e * 7315560))) + (e * (e * 15974580)))) + (e * (e * (e * 21647550))))) + (e * (e * (e * (e * 18081760)))))) + (e * (e * (e * (e * (e * 9132870))))))) + (e * (e * (e * (e * (e * (e * 2591880)))))))) + (e * (e * (e * (e * (e * (e * (e * 321200)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 388870) + (e * 1555480))) + (e * (e * 4180100)))) + (e * (e * (e * 7096120))))) + (e * (e * (e * (e * 7657000)))))) + (e * (e * (e * (e * (e * 5301860))))))) + (e * (e * (e * (e * (e * (e * 2309290)))))))) + (e * (e * (e * (e * (e * (e * (e * 581800))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 29380) + (e * 132210))) + (e * (e * 445680)))) + (e * (e * (e * 942900))))) + (e * (e * (e * (e * 1278840)))))) + (e * (e * (e * (e * (e * 1148340))))))) + (e * (e * (e * (e * (e * (e * 686160)))))))) + (e * (e * (e * (e * (e * (e * (e * 264210))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong3_part_1_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_0 c d e := by
  unfold strong3_part_1_0
  positivity

theorem strong3_part_1_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 0 = strong3_part_1_0 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_0 <;> ring

def strong3_part_1_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 5880800) + ((d * 28369540) + (e * 13891800)))) + ((d * ((d * 67145140) + (e * 65771300))) + (e * (e * 19413760))))) + ((d * ((d * ((d * 98888400) + (e * 145054440))) + (e * (e * 90884300)))) + (e * (e * (e * 21725780)))))) + ((d * ((d * ((d * ((d * 95947400) + (e * 186911120))) + (e * (e * 182068180)))) + (e * (e * (e * 90455460))))) + (e * (e * (e * (e * 17877400))))))) + ((d * ((d * ((d * ((d * ((d * 61035160) + (e * 147655960))) + (e * (e * 196372100)))) + (e * (e * (e * 150076160))))) + (e * (e * (e * (e * 60283120)))))) + (e * (e * (e * (e * (e * 9883220)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 24333120) + (e * 69952560))) + (e * (e * 118656300)))) + (e * (e * (e * 123546500))))) + (e * (e * (e * (e * 75612480)))))) + (e * (e * (e * (e * (e * 25077360))))))) + (e * (e * (e * (e * (e * (e * 3517280))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 5459860) + (e * 18050080))) + (e * (e * 37637160)))) + (e * (e * (e * 50227880))))) + (e * (e * (e * (e * 41756640)))))) + (e * (e * (e * (e * (e * 21077280))))))) + (e * (e * (e * (e * (e * (e * 5985460)))))))) + (e * (e * (e * (e * (e * (e * (e * 741940)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 517180) + (e * 1910540))) + (e * (e * 4821760)))) + (e * (e * (e * 8001240))))) + (e * (e * (e * (e * 8529920)))))) + (e * (e * (e * (e * (e * 5856520))))))) + (e * (e * (e * (e * (e * (e * 2534620)))))))) + (e * (e * (e * (e * (e * (e * (e * 635180))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 70680))))))))))

private theorem strong3_part_1_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_1 c d e := by
  unfold strong3_part_1_1
  positivity

theorem strong3_part_1_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 1 = strong3_part_1_1 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_1 <;> ring

def strong3_part_1_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 26633280) + ((d * 114949300) + (e * 55679680)))) + ((d * ((d * 239297110) + (e * 231903440))) + (e * (e * 69984040))))) + ((d * ((d * ((d * 301036640) + (e * 436003970))) + (e * (e * 275521820)))) + (e * (e * (e * 67562780)))))) + ((d * ((d * ((d * ((d * 238621930) + (e * 457024180))) + (e * (e * 442922950)))) + (e * (e * (e * 222497280))))) + (e * (e * (e * (e * 44684260))))))) + ((d * ((d * ((d * ((d * ((d * 115845940) + (e * 273766790))) + (e * (e * 357462820)))) + (e * (e * (e * 273116410))))) + (e * (e * (e * (e * 110522080)))))) + (e * (e * (e * (e * (e * 18281520)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 31270130) + (e * 87038060))) + (e * (e * 143009950)))) + (e * (e * (e * 147470760))))) + (e * (e * (e * (e * 90257040)))))) + (e * (e * (e * (e * (e * 30002820))))))) + (e * (e * (e * (e * (e * (e * 4212970))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3566220) + (e * 11277370))) + (e * (e * 22438980)))) + (e * (e * (e * 29411710))))) + (e * (e * (e * (e * 24296360)))))) + (e * (e * (e * (e * (e * 12214620))))))) + (e * (e * (e * (e * (e * (e * 3450840)))))))) + (e * (e * (e * (e * (e * (e * (e * 424350)))))))))

private theorem strong3_part_1_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_2 c d e := by
  unfold strong3_part_1_2
  positivity

theorem strong3_part_1_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 2 = strong3_part_1_2 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_2 <;> ring

def strong3_part_1_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 70178720) + ((d * 265136360) + (e * 128126420)))) + ((d * ((d * 471665220) + (e * 455918520))) + (e * (e * 141226920))))) + ((d * ((d * ((d * 486379820) + (e * 700900240))) + (e * (e * 447923800)))) + (e * (e * (e * 112358780)))))) + ((d * ((d * ((d * ((d * 295287680) + (e * 560162860))) + (e * (e * 541164780)))) + (e * (e * (e * 274186880))))) + (e * (e * (e * (e * 55679720))))))) + ((d * ((d * ((d * ((d * ((d * 97293000) + (e * 226345540))) + (e * (e * 290585660)))) + (e * (e * (e * 221395320))))) + (e * (e * (e * (e * 89900180)))))) + (e * (e * (e * (e * (e * 14922600)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 13344420) + (e * 36290640))) + (e * (e * 57823280)))) + (e * (e * (e * 58880620))))) + (e * (e * (e * (e * 35925980)))))) + (e * (e * (e * (e * (e * 11922420))))))) + (e * (e * (e * (e * (e * (e * 1666860))))))))

private theorem strong3_part_1_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_3 c d e := by
  unfold strong3_part_1_3
  positivity

theorem strong3_part_1_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 3 = strong3_part_1_3 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_3 <;> ring

def strong3_part_1_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 118962400) + ((d * 381881280) + (e * 185376660)))) + ((d * ((d * 556448550) + (e * 539909260))) + (e * (e * 171972910))))) + ((d * ((d * ((d * 440379780) + (e * 635125330))) + (e * (e * 410975420)))) + (e * (e * (e * 105037670)))))) + ((d * ((d * ((d * ((d * 181862720) + (e * 343655480))) + (e * (e * 331312660)))) + (e * (e * (e * 168791600))))) + (e * (e * (e * (e * 34491630))))))) + ((d * ((d * ((d * ((d * ((d * 30483720) + (e * 70244220))) + (e * (e * 88786100)))) + (e * (e * (e * 67277980))))) + (e * (e * (e * (e * 27310160)))))) + (e * (e * (e * (e * (e * 4528890)))))))

private theorem strong3_part_1_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_4 c d e := by
  unfold strong3_part_1_4
  positivity

theorem strong3_part_1_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 4 = strong3_part_1_4 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_4 <;> ring

def strong3_part_1_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 135190920) + ((d * 353142600) + (e * 173004580)))) + ((d * ((d * 393954640) + (e * 385409720))) + (e * (e * 126163360))))) + ((d * ((d * ((d * 212139580) + (e * 307523200))) + (e * (e * 201440720)))) + (e * (e * (e * 52213080)))))) + ((d * ((d * ((d * ((d * 44616900) + (e * 84341300))) + (e * (e * 81160720)))) + (e * (e * (e * 41436320))))) + (e * (e * (e * (e * 8480280))))))

private theorem strong3_part_1_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_5 c d e := by
  unfold strong3_part_1_5
  positivity

theorem strong3_part_1_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 5 = strong3_part_1_5 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_5 <;> ring

def strong3_part_1_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 103836250) + ((d * 206153500) + (e * 102103750)))) + ((d * ((d * 155676640) + (e * 153944140))) + (e * (e * 51626890))))) + ((d * ((d * ((d * 42589260) + (e * 62258140))) + (e * (e * 41209140)))) + (e * (e * (e * 10770130)))))

private theorem strong3_part_1_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_6 c d e := by
  unfold strong3_part_1_6
  positivity

theorem strong3_part_1_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 6 = strong3_part_1_6 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_6 <;> ring

def strong3_part_1_7 (c d e : ℝ) : ℝ :=
  ((c * ((c * 52678940) + ((d * 70258920) + (e * 35098960)))) + ((d * ((d * 26691000) + (e * 26691000))) + (e * (e * 9111020))))

private theorem strong3_part_1_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_7 c d e := by
  unfold strong3_part_1_7
  positivity

theorem strong3_part_1_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 7 = strong3_part_1_7 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_7 <;> ring

def strong3_part_1_8 (c d e : ℝ) : ℝ :=
  ((c * 16337970) + ((d * 10891980) + (e * 5445990)))

private theorem strong3_part_1_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_8 c d e := by
  unfold strong3_part_1_8
  positivity

theorem strong3_part_1_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 8 = strong3_part_1_8 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_8 <;> ring

def strong3_part_1_9 (c d e : ℝ) : ℝ :=
  2420440

private theorem strong3_part_1_9_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_1_9 c d e := by
  unfold strong3_part_1_9
  positivity

theorem strong3_part_1_9_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 1) 9 = strong3_part_1_9 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_1_9 <;> ring

theorem strong3_coeff_1_length (c d e : ℝ) :
    (chamberPoly3 c d e 1).length ≤ 10 := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong3_coeff_1_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly3 c d e 1) b := by
  apply polyEval_nonneg_of_coeff _ b 10
    (strong3_coeff_1_length c d e) hb
  apply forall_fin10
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 0
    rw [strong3_part_1_0_eq]
    exact strong3_part_1_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 1
    rw [strong3_part_1_1_eq]
    exact strong3_part_1_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 2
    rw [strong3_part_1_2_eq]
    exact strong3_part_1_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 3
    rw [strong3_part_1_3_eq]
    exact strong3_part_1_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 4
    rw [strong3_part_1_4_eq]
    exact strong3_part_1_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 5
    rw [strong3_part_1_5_eq]
    exact strong3_part_1_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 6
    rw [strong3_part_1_6_eq]
    exact strong3_part_1_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 7
    rw [strong3_part_1_7_eq]
    exact strong3_part_1_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 8
    rw [strong3_part_1_8_eq]
    exact strong3_part_1_8_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 1) 9
    rw [strong3_part_1_9_eq]
    exact strong3_part_1_9_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
