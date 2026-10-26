module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a^1`

Generated certificate. The coefficient of `a^1` (a power of the smallest weight) in the chamber
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

def strong4_part_1_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 573910) + ((d * 3643980) + (e * 2122770)))) + ((d * ((d * 10818690) + (e * 12829820))) + (e * (e * 4338740))))) + ((d * ((d * ((d * 18979560) + (e * 34086390))) + (e * (e * 23734120)))) + (e * (e * (e * 5699020)))))) + ((d * ((d * ((d * ((d * 21298270) + (e * 51179140))) + (e * (e * 54823440)))) + (e * (e * (e * 27061720))))) + (e * (e * (e * (e * 4982330))))))) + ((d * ((d * ((d * ((d * ((d * 15692420) + (e * 47021590))) + (e * (e * 68873600)))) + (e * (e * (e * 52502600))))) + (e * (e * (e * (e * 19949300)))))) + (e * (e * (e * (e * (e * 2997390)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 7548430) + (e * 26853980))) + (e * (e * 50525170)))) + (e * (e * (e * 53049520))))) + (e * (e * (e * (e * 31299960)))))) + (e * (e * (e * (e * (e * 9752760))))))) + (e * (e * (e * (e * (e * (e * 1252660))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2280680) + (e * 9234610))) + (e * (e * 21499020)))) + (e * (e * (e * 29299270))))) + (e * (e * (e * (e * 23976840)))))) + (e * (e * (e * (e * (e * 11676000))))))) + (e * (e * (e * (e * (e * (e * 3132760)))))))) + (e * (e * (e * (e * (e * (e * (e * 358220)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 392730) + (e * 1729100))) + (e * (e * 4868680)))) + (e * (e * (e * 8331340))))) + (e * (e * (e * (e * 8921020)))))) + (e * (e * (e * (e * (e * 6070640))))))) + (e * (e * (e * (e * (e * (e * 2567470)))))))) + (e * (e * (e * (e * (e * (e * (e * 618820))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 29380) + (e * 132210))) + (e * (e * 445680)))) + (e * (e * (e * 942900))))) + (e * (e * (e * (e * 1278840)))))) + (e * (e * (e * (e * (e * 1148340))))))) + (e * (e * (e * (e * (e * (e * 686160)))))))) + (e * (e * (e * (e * (e * (e * (e * 264210))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong4_part_1_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_0 c d e := by
  unfold strong4_part_1_0
  positivity

theorem strong4_part_1_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 0 = strong4_part_1_0 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_0 <;> ring

def strong4_part_1_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 5880800) + ((d * 32568660) + (e * 18676860)))) + ((d * ((d * 84105820) + (e * 97912820))) + (e * (e * 33220760))))) + ((d * ((d * ((d * 127025380) + (e * 222547840))) + (e * (e * 154795140)))) + (e * (e * (e * 37546900)))))) + ((d * ((d * ((d * ((d * 120313100) + (e * 279511740))) + (e * (e * 297294420)))) + (e * (e * (e * 147622980))))) + (e * (e * (e * (e * 27404600))))))) + ((d * ((d * ((d * ((d * ((d * 72461660) + (e * 207441400))) + (e * (e * 299209260)))) + (e * (e * (e * 228345740))))) + (e * (e * (e * (e * 87163580)))))) + (e * (e * (e * (e * (e * 13164140)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 26995100) + (e * 90398020))) + (e * (e * 165644460)))) + (e * (e * (e * 173113940))))) + (e * (e * (e * (e * 102176980)))))) + (e * (e * (e * (e * (e * 31894500))))))) + (e * (e * (e * (e * (e * (e * 4107200))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 5689480) + (e * 21310380))) + (e * (e * 47598180)))) + (e * (e * (e * 64110240))))) + (e * (e * (e * (e * 52229020)))))) + (e * (e * (e * (e * (e * 25383240))))))) + (e * (e * (e * (e * (e * (e * 6808080)))))))) + (e * (e * (e * (e * (e * (e * (e * 778960)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 521040) + (e * 2084160))) + (e * (e * 5510340)))) + (e * (e * (e * 9236460))))) + (e * (e * (e * (e * 9793940)))))) + (e * (e * (e * (e * (e * 6625300))))))) + (e * (e * (e * (e * (e * (e * 2792800)))))))) + (e * (e * (e * (e * (e * (e * (e * 672200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 70680))))))))))

private theorem strong4_part_1_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_1 c d e := by
  unfold strong4_part_1_1
  positivity

theorem strong4_part_1_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 1 = strong4_part_1_1 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_1 <;> ring

def strong4_part_1_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 26633280) + ((d * 127163340) + (e * 71483660)))) + ((d * ((d * 281058870) + (e * 319975020))) + (e * (e * 108900190))))) + ((d * ((d * ((d * 357017340) + (e * 607884950))) + (e * (e * 421804600)))) + (e * (e * (e * 103374210)))))) + ((d * ((d * ((d * ((d * 275290340) + (e * 616259760))) + (e * (e * 649080390)))) + (e * (e * (e * 324051980))))) + (e * (e * (e * (e * 60625270))))))) + ((d * ((d * ((d * ((d * ((d * 127538340) + (e * 348247660))) + (e * (e * 492625900)))) + (e * (e * (e * 375835890))))) + (e * (e * (e * (e * 144031320)))))) + (e * (e * (e * (e * (e * 21830490)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 32766200) + (e * 103519720))) + (e * (e * 183746410)))) + (e * (e * (e * 190666860))))) + (e * (e * (e * (e * 112487630)))))) + (e * (e * (e * (e * (e * 35120880))))))) + (e * (e * (e * (e * (e * (e * 4520190))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3605320) + (e * 12618620))) + (e * (e * 26875560)))) + (e * (e * (e * 35642350))))) + (e * (e * (e * (e * 28873660)))))) + (e * (e * (e * (e * (e * 13977450))))))) + (e * (e * (e * (e * (e * (e * 3732580)))))))) + (e * (e * (e * (e * (e * (e * (e * 424350)))))))))

private theorem strong4_part_1_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_2 c d e := by
  unfold strong4_part_1_2
  positivity

theorem strong4_part_1_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 2 = strong4_part_1_2 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_2 <;> ring

def strong4_part_1_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 70178720) + ((d * 284062380) + (e * 155935960)))) + ((d * ((d * 524604720) + (e * 582042020))) + (e * (e * 198664220))))) + ((d * ((d * ((d * 540324880) + (e * 891440180))) + (e * (e * 615965940)))) + (e * (e * (e * 152491860)))))) + ((d * ((d * ((d * ((d * 319071760) + (e * 687099040))) + (e * (e * 714368160)))) + (e * (e * (e * 358117900))))) + (e * (e * (e * (e * 67456740))))))) + ((d * ((d * ((d * ((d * ((d * 101232800) + (e * 263981340))) + (e * (e * 364752800)))) + (e * (e * (e * 277537420))))) + (e * (e * (e * (e * 106650060)))))) + (e * (e * (e * (e * (e * 16194300)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 13431720) + (e * 40295160))) + (e * (e * 69003140)))) + (e * (e * (e * 70847680))))) + (e * (e * (e * (e * 41709320)))))) + (e * (e * (e * (e * (e * 13001340))))))) + (e * (e * (e * (e * (e * (e * 1666860))))))))

private theorem strong4_part_1_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_3 c d e := by
  unfold strong4_part_1_3
  positivity

theorem strong4_part_1_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 3 = strong4_part_1_3 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_3 <;> ring

def strong4_part_1_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 118962400) + ((d * 398307380) + (e * 212930720)))) + ((d * ((d * 592117720) + (e * 638692240))) + (e * (e * 218547430))))) + ((d * ((d * ((d * 464940680) + (e * 742164900))) + (e * (e * 509564080)))) + (e * (e * (e * 127302190)))))) + ((d * ((d * ((d * ((d * 187165650) + (e * 387909720))) + (e * (e * 396816810)))) + (e * (e * (e * 199316800))))) + (e * (e * (e * (e * 37735690))))))) + ((d * ((d * ((d * ((d * ((d * 30468820) + (e * 76172050))) + (e * (e * 102473920)))) + (e * (e * (e * 77538830))))) + (e * (e * (e * (e * 29825920)))))) + (e * (e * (e * (e * (e * 4528890)))))))

private theorem strong4_part_1_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_4 c d e := by
  unfold strong4_part_1_4
  positivity

theorem strong4_part_1_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 4 = strong4_part_1_4 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_4 <;> ring

def strong4_part_1_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 135190920) + ((d * 360625660) + (e * 187621080)))) + ((d * ((d * 405439740) + (e * 424948740))) + (e * (e * 145672360))))) + ((d * ((d * ((d * 215922160) + (e * 333637740))) + (e * (e * 227034240)))) + (e * (e * (e * 57105580)))))) + ((d * ((d * ((d * ((d * 44397440) + (e * 88794880))) + (e * (e * 89095320)))) + (e * (e * (e * 44697880))))) + (e * (e * (e * (e * 8480280))))))

private theorem strong4_part_1_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_5 c d e := by
  unfold strong4_part_1_5
  positivity

theorem strong4_part_1_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 5 = strong4_part_1_5 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_5 <;> ring

def strong4_part_1_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 103836250) + ((d * 207459000) + (e * 105355250)))) + ((d * ((d * 156768640) + (e * 160020140))) + (e * (e * 54878390))))) + ((d * ((d * ((d * 42375760) + (e * 63563640))) + (e * (e * 42728140)))) + (e * (e * (e * 10770130)))))

private theorem strong4_part_1_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_6 c d e := by
  unfold strong4_part_1_6
  positivity

theorem strong4_part_1_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 6 = strong4_part_1_6 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_6 <;> ring

def strong4_part_1_7 (c d e : ℝ) : ℝ :=
  ((c * ((c * 52678940) + ((d * 70197920) + (e * 35098960)))) + ((d * ((d * 26630000) + (e * 26630000))) + (e * (e * 9111020))))

private theorem strong4_part_1_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_7 c d e := by
  unfold strong4_part_1_7
  positivity

theorem strong4_part_1_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 7 = strong4_part_1_7 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_7 <;> ring

def strong4_part_1_8 (c d e : ℝ) : ℝ :=
  ((c * 16337970) + ((d * 10891980) + (e * 5445990)))

private theorem strong4_part_1_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_8 c d e := by
  unfold strong4_part_1_8
  positivity

theorem strong4_part_1_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 8 = strong4_part_1_8 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_8 <;> ring

def strong4_part_1_9 (c d e : ℝ) : ℝ :=
  2420440

private theorem strong4_part_1_9_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_1_9 c d e := by
  unfold strong4_part_1_9
  positivity

theorem strong4_part_1_9_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 1) 9 = strong4_part_1_9 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong4_part_1_9 <;> ring

theorem strong4_coeff_1_length (c d e : ℝ) :
    (chamberPoly4 c d e 1).length ≤ 10 := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong4_coeff_1_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly4 c d e 1) b := by
  apply polyEval_nonneg_of_coeff _ b 10
    (strong4_coeff_1_length c d e) hb
  apply forall_fin10
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 0
    rw [strong4_part_1_0_eq]
    exact strong4_part_1_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 1
    rw [strong4_part_1_1_eq]
    exact strong4_part_1_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 2
    rw [strong4_part_1_2_eq]
    exact strong4_part_1_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 3
    rw [strong4_part_1_3_eq]
    exact strong4_part_1_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 4
    rw [strong4_part_1_4_eq]
    exact strong4_part_1_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 5
    rw [strong4_part_1_5_eq]
    exact strong4_part_1_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 6
    rw [strong4_part_1_6_eq]
    exact strong4_part_1_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 7
    rw [strong4_part_1_7_eq]
    exact strong4_part_1_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 8
    rw [strong4_part_1_8_eq]
    exact strong4_part_1_8_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly4 c d e 1) 9
    rw [strong4_part_1_9_eq]
    exact strong4_part_1_9_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
