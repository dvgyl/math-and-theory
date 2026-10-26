module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a^1`

Generated certificate. The coefficient of `a^1` (a power of the smallest weight) in the chamber
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

def strong5_part_1_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 573910) + ((d * 3643980) + (e * 1521210)))) + ((d * ((d * 10818690) + (e * 8807560))) + (e * (e * 2327610))))) + ((d * ((d * ((d * 18979560) + (e * 22852290))) + (e * (e * 12500020)))) + (e * (e * (e * 2928270)))))) + ((d * ((d * ((d * ((d * 21298270) + (e * 34013940))) + (e * (e * 29075640)))) + (e * (e * (e * 14240820))))) + (e * (e * (e * (e * 2863180))))))) + ((d * ((d * ((d * ((d * ((d * 15692420) + (e * 31440510))) + (e * (e * 37711440)))) + (e * (e * (e * 28912860))))) + (e * (e * (e * (e * 11940640)))))) + (e * (e * (e * (e * (e * 1993740)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 7548430) + (e * 18436600))) + (e * (e * 29481720)))) + (e * (e * (e * 31479960))))) + (e * (e * (e * (e * 19989070)))))) + (e * (e * (e * (e * (e * 6819960))))))) + (e * (e * (e * (e * (e * (e * 969960))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2280680) + (e * 6730150))) + (e * (e * 13985640)))) + (e * (e * (e * 19500480))))) + (e * (e * (e * (e * 16901560)))))) + (e * (e * (e * (e * (e * 8824230))))))) + (e * (e * (e * (e * (e * (e * 2566400)))))))) + (e * (e * (e * (e * (e * (e * (e * 321200)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 392730) + (e * 1412740))) + (e * (e * 3761420)))) + (e * (e * (e * 6562520))))) + (e * (e * (e * (e * 7267120)))))) + (e * (e * (e * (e * (e * 5148020))))))) + (e * (e * (e * (e * (e * (e * 2283810)))))))) + (e * (e * (e * (e * (e * (e * (e * 581800))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 29380) + (e * 132210))) + (e * (e * 445680)))) + (e * (e * (e * 942900))))) + (e * (e * (e * (e * 1278840)))))) + (e * (e * (e * (e * (e * 1148340))))))) + (e * (e * (e * (e * (e * (e * 686160)))))))) + (e * (e * (e * (e * (e * (e * (e * 264210))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong5_part_1_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_0 c d e := by
  unfold strong5_part_1_0
  positivity

theorem strong5_part_1_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 0 = strong5_part_1_0 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_0 <;> ring

def strong5_part_1_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 5880800) + ((d * 32568660) + (e * 13891800)))) + ((d * ((d * 84105820) + (e * 70298820))) + (e * (e * 19413760))))) + ((d * ((d * ((d * 127025380) + (e * 158528300))) + (e * (e * 90775600)))) + (e * (e * (e * 21725780)))))) + ((d * ((d * ((d * ((d * 120313100) + (e * 201740660))) + (e * (e * 180637800)))) + (e * (e * (e * 89683040))))) + (e * (e * (e * (e * 17877400))))))) + ((d * ((d * ((d * ((d * ((d * 72461660) + (e * 154866900))) + (e * (e * 194060260)))) + (e * (e * (e * 149250240))))) + (e * (e * (e * (e * 60642580)))))) + (e * (e * (e * (e * (e * 9883220)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 26995100) + (e * 71572580))) + (e * (e * 118580860)))) + (e * (e * (e * 125385700))))) + (e * (e * (e * (e * 77648220)))))) + (e * (e * (e * (e * (e * 25675980))))))) + (e * (e * (e * (e * (e * (e * 3517280))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 5689480) + (e * 18515980))) + (e * (e * 39214980)))) + (e * (e * (e * 53356760))))) + (e * (e * (e * (e * 44694060)))))) + (e * (e * (e * (e * (e * 22447560))))))) + (e * (e * (e * (e * (e * (e * 6242680)))))))) + (e * (e * (e * (e * (e * (e * (e * 741940)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 521040) + (e * 2084160))) + (e * (e * 5510340)))) + (e * (e * (e * 9236460))))) + (e * (e * (e * (e * 9793940)))))) + (e * (e * (e * (e * (e * 6625300))))))) + (e * (e * (e * (e * (e * (e * 2792800)))))))) + (e * (e * (e * (e * (e * (e * (e * 672200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 70680))))))))))

private theorem strong5_part_1_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_1 c d e := by
  unfold strong5_part_1_1
  positivity

theorem strong5_part_1_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 1 = strong5_part_1_1 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_1 <;> ring

def strong5_part_1_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 26633280) + ((d * 127163340) + (e * 55679680)))) + ((d * ((d * 281058870) + (e * 242142720))) + (e * (e * 69984040))))) + ((d * ((d * ((d * 357017340) + (e * 463167070))) + (e * (e * 277086720)))) + (e * (e * (e * 67562780)))))) + ((d * ((d * ((d * ((d * 275290340) + (e * 484901600))) + (e * (e * 452043150)))) + (e * (e * (e * 226490880))))) + (e * (e * (e * (e * 44684260))))))) + ((d * ((d * ((d * ((d * ((d * 127538340) + (e * 289444040))) + (e * (e * 375018660)))) + (e * (e * (e * 287939250))))) + (e * (e * (e * (e * 114938300)))))) + (e * (e * (e * (e * (e * 18281520)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 32766200) + (e * 93077480))) + (e * (e * 157640810)))) + (e * (e * (e * 164445580))))) + (e * (e * (e * (e * 99261310)))))) + (e * (e * (e * (e * (e * 31838040))))))) + (e * (e * (e * (e * (e * (e * 4212970))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3605320) + (e * 12618620))) + (e * (e * 26875560)))) + (e * (e * (e * 35642350))))) + (e * (e * (e * (e * 28873660)))))) + (e * (e * (e * (e * (e * 13977450))))))) + (e * (e * (e * (e * (e * (e * 3732580)))))))) + (e * (e * (e * (e * (e * (e * (e * 424350)))))))))

private theorem strong5_part_1_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_2 c d e := by
  unfold strong5_part_1_2
  positivity

theorem strong5_part_1_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 2 = strong5_part_1_2 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_2 <;> ring

def strong5_part_1_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 70178720) + ((d * 284062380) + (e * 128126420)))) + ((d * ((d * 524604720) + (e * 467167420))) + (e * (e * 141226920))))) + ((d * ((d * ((d * 540324880) + (e * 729534460))) + (e * (e * 454060220)))) + (e * (e * (e * 112358780)))))) + ((d * ((d * ((d * ((d * 319071760) + (e * 589188000))) + (e * (e * 567501600)))) + (e * (e * (e * 285608340))))) + (e * (e * (e * (e * 55679720))))))) + ((d * ((d * ((d * ((d * ((d * 101232800) + (e * 242182660))) + (e * (e * 321155440)))) + (e * (e * (e * 245160940))))) + (e * (e * (e * (e * 96072260)))))) + (e * (e * (e * (e * (e * 14922600)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 13431720) + (e * 40295160))) + (e * (e * 69003140)))) + (e * (e * (e * 70847680))))) + (e * (e * (e * (e * 41709320)))))) + (e * (e * (e * (e * (e * 13001340))))))) + (e * (e * (e * (e * (e * (e * 1666860))))))))

private theorem strong5_part_1_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_3 c d e := by
  unfold strong5_part_1_3
  positivity

theorem strong5_part_1_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 3 = strong5_part_1_3 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_3 <;> ring

def strong5_part_1_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 118962400) + ((d * 398307380) + (e * 185376660)))) + ((d * ((d * 592117720) + (e * 545543200))) + (e * (e * 171972910))))) + ((d * ((d * ((d * 464940680) + (e * 652657140))) + (e * (e * 420056320)))) + (e * (e * (e * 105037670)))))) + ((d * ((d * ((d * ((d * 187165650) + (e * 360752880))) + (e * (e * 356081550)))) + (e * (e * (e * 179250260))))) + (e * (e * (e * (e * 34491630))))))) + ((d * ((d * ((d * ((d * ((d * 30468820) + (e * 76172050))) + (e * (e * 102473920)))) + (e * (e * (e * 77538830))))) + (e * (e * (e * (e * 29825920)))))) + (e * (e * (e * (e * (e * 4528890)))))))

private theorem strong5_part_1_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_4 c d e := by
  unfold strong5_part_1_4
  positivity

theorem strong5_part_1_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 4 = strong5_part_1_4 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_4 <;> ring

def strong5_part_1_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 135190920) + ((d * 360625660) + (e * 173004580)))) + ((d * ((d * 405439740) + (e * 385930740))) + (e * (e * 126163360))))) + ((d * ((d * ((d * 215922160) + (e * 314128740))) + (e * (e * 207525240)))) + (e * (e * (e * 52213080)))))) + ((d * ((d * ((d * ((d * 44397440) + (e * 88794880))) + (e * (e * 89095320)))) + (e * (e * (e * 44697880))))) + (e * (e * (e * (e * 8480280))))))

private theorem strong5_part_1_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_5 c d e := by
  unfold strong5_part_1_5
  positivity

theorem strong5_part_1_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 5 = strong5_part_1_5 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_5 <;> ring

def strong5_part_1_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 103836250) + ((d * 207459000) + (e * 102103750)))) + ((d * ((d * 156768640) + (e * 153517140))) + (e * (e * 51626890))))) + ((d * ((d * ((d * 42375760) + (e * 63563640))) + (e * (e * 42728140)))) + (e * (e * (e * 10770130)))))

private theorem strong5_part_1_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_6 c d e := by
  unfold strong5_part_1_6
  positivity

theorem strong5_part_1_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 6 = strong5_part_1_6 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_6 <;> ring

def strong5_part_1_7 (c d e : ℝ) : ℝ :=
  ((c * ((c * 52678940) + ((d * 70197920) + (e * 35098960)))) + ((d * ((d * 26630000) + (e * 26630000))) + (e * (e * 9111020))))

private theorem strong5_part_1_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_7 c d e := by
  unfold strong5_part_1_7
  positivity

theorem strong5_part_1_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 7 = strong5_part_1_7 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_7 <;> ring

def strong5_part_1_8 (c d e : ℝ) : ℝ :=
  ((c * 16337970) + ((d * 10891980) + (e * 5445990)))

private theorem strong5_part_1_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_8 c d e := by
  unfold strong5_part_1_8
  positivity

theorem strong5_part_1_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 8 = strong5_part_1_8 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_8 <;> ring

def strong5_part_1_9 (c d e : ℝ) : ℝ :=
  2420440

private theorem strong5_part_1_9_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_1_9 c d e := by
  unfold strong5_part_1_9
  positivity

theorem strong5_part_1_9_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 1) 9 = strong5_part_1_9 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong5_part_1_9 <;> ring

theorem strong5_coeff_1_length (c d e : ℝ) :
    (chamberPoly5 c d e 1).length ≤ 10 := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong5_coeff_1_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly5 c d e 1) b := by
  apply polyEval_nonneg_of_coeff _ b 10
    (strong5_coeff_1_length c d e) hb
  apply forall_fin10
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 0
    rw [strong5_part_1_0_eq]
    exact strong5_part_1_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 1
    rw [strong5_part_1_1_eq]
    exact strong5_part_1_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 2
    rw [strong5_part_1_2_eq]
    exact strong5_part_1_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 3
    rw [strong5_part_1_3_eq]
    exact strong5_part_1_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 4
    rw [strong5_part_1_4_eq]
    exact strong5_part_1_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 5
    rw [strong5_part_1_5_eq]
    exact strong5_part_1_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 6
    rw [strong5_part_1_6_eq]
    exact strong5_part_1_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 7
    rw [strong5_part_1_7_eq]
    exact strong5_part_1_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 8
    rw [strong5_part_1_8_eq]
    exact strong5_part_1_8_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly5 c d e 1) 9
    rw [strong5_part_1_9_eq]
    exact strong5_part_1_9_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
