module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a^2`

Generated certificate. The coefficient of `a^2` (a power of the smallest weight) in the chamber
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

def strong1_part_2_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 3298205) + ((d * 18285710) + (e * 10185780)))) + ((d * ((d * 47604275) + (e * 53685400))) + (e * (e * 18035170))))) + ((d * ((d * ((d * 72750900) + (e * 123507010))) + (e * (e * 84780270)))) + (e * (e * (e * 20449840)))))) + ((d * ((d * ((d * ((d * 69859825) + (e * 157527250))) + (e * (e * 164784750)))) + (e * (e * (e * 81022150))))) + (e * (e * (e * (e * 14948775))))))) + ((d * ((d * ((d * ((d * ((d * 42723780) + (e * 119067230))) + (e * (e * 168242930)))) + (e * (e * (e * 126559420))))) + (e * (e * (e * (e * 47820950)))))) + (e * (e * (e * (e * (e * 7169360)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 16182515) + (e * 53014870))) + (e * (e * 94722795)))) + (e * (e * (e * 97099170))))) + (e * (e * (e * (e * 56494270)))))) + (e * (e * (e * (e * (e * 17438670))))))) + (e * (e * (e * (e * (e * (e * 2228210))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3469070) + (e * 12816430))) + (e * (e * 27755640)))) + (e * (e * (e * 36470430))))) + (e * (e * (e * (e * 29159820)))))) + (e * (e * (e * (e * (e * 13956990))))))) + (e * (e * (e * (e * (e * (e * 3700800)))))))) + (e * (e * (e * (e * (e * (e * (e * 420740)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 322745) + (e * 1290980))) + (e * (e * 3285340)))) + (e * (e * (e * 5337590))))) + (e * (e * (e * (e * 5528370)))))) + (e * (e * (e * (e * (e * 3666900))))))) + (e * (e * (e * (e * (e * (e * 1521805)))))))) + (e * (e * (e * (e * (e * (e * (e * 362790))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 38105))))))))))

private theorem strong1_part_2_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_0 c d e := by
  unfold strong1_part_2_0
  positivity

theorem strong1_part_2_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 0 = strong1_part_2_0 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_0 <;> ring

def strong1_part_2_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 29641340) + ((d * 143470300) + (e * 77912070)))) + ((d * ((d * 322989500) + (e * 354055180))) + (e * (e * 118973670))))) + ((d * ((d * ((d * 417452110) + (e * 689274980))) + (e * (e * 470973240)))) + (e * (e * (e * 114000400)))))) + ((d * ((d * ((d * ((d * 326140530) + (e * 716860740))) + (e * (e * 742870410)))) + (e * (e * (e * 364472740))))) + (e * (e * (e * (e * 67315950))))))) + ((d * ((d * ((d * ((d * ((d * 152209010) + (e * 414908100))) + (e * (e * 577936180)))) + (e * (e * (e * 431467260))))) + (e * (e * (e * (e * 162477480)))))) + (e * (e * (e * (e * (e * 24341880)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 39095550) + (e * 125898720))) + (e * (e * 220589740)))) + (e * (e * (e * 223189260))))) + (e * (e * (e * (e * 128864980)))))) + (e * (e * (e * (e * (e * 39615420))))))) + (e * (e * (e * (e * (e * (e * 5058890))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 4256810) + (e * 15573520))) + (e * (e * 32884470)))) + (e * (e * (e * 42399780))))) + (e * (e * (e * (e * 33498010)))))) + (e * (e * (e * (e * (e * 15913470))))))) + (e * (e * (e * (e * (e * (e * 4204860)))))))) + (e * (e * (e * (e * (e * (e * (e * 478690)))))))))

private theorem strong1_part_2_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_1 c d e := by
  unfold strong1_part_2_1
  positivity

theorem strong1_part_2_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 1 = strong1_part_2_1 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_1 <;> ring

def strong1_part_2_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 115745920) + ((d * 477678930) + (e * 253650330)))) + ((d * ((d * 902931490) + (e * 965336710))) + (e * (e * 326738295))))) + ((d * ((d * ((d * 947146890) + (e * 1527257550))) + (e * (e * 1044878850)))) + (e * (e * (e * 254942940)))))) + ((d * ((d * ((d * ((d * 564174450) + (e * 1214458230))) + (e * (e * 1253062525)))) + (e * (e * (e * 615715400))))) + (e * (e * (e * (e * 114153685))))))) + ((d * ((d * ((d * ((d * ((d * 178398430) + (e * 477936660))) + (e * (e * 659324600)))) + (e * (e * (e * 490090450))))) + (e * (e * (e * (e * 184389820)))))) + (e * (e * (e * (e * (e * 27672240)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 23252285) + (e * 73901600))) + (e * (e * 127575580)))) + (e * (e * (e * 127811110))))) + (e * (e * (e * (e * 73409085)))))) + (e * (e * (e * (e * (e * 22524240))))))) + (e * (e * (e * (e * (e * (e * 2879895))))))))

private theorem strong1_part_2_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_2 c d e := by
  unfold strong1_part_2_2
  positivity

theorem strong1_part_2_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 2 = strong1_part_2_2 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_2 <;> ring

def strong1_part_2_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 257388470) + ((d * 878403610) + (e * 457343610)))) + ((d * ((d * 1337357250) + (e * 1398564200))) + (e * (e * 479727820))))) + ((d * ((d * ((d * 1067764310) + (e * 1687081630))) + (e * (e * 1160883620)))) + (e * (e * (e * 286354250)))))) + ((d * ((d * ((d * ((d * 431232060) + (e * 912387460))) + (e * (e * 940217460)))) + (e * (e * (e * 463581000))))) + (e * (e * (e * (e * 86391430))))))) + ((d * ((d * ((d * ((d * ((d * 69289360) + (e * 183036190))) + (e * (e * 250597290)))) + (e * (e * (e * 185691120))))) + (e * (e * (e * (e * 69881660)))))) + (e * (e * (e * (e * (e * 10520500)))))))

private theorem strong1_part_2_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_3 c d e := by
  unfold strong1_part_2_3
  positivity

theorem strong1_part_2_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 3 = strong1_part_2_3 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_3 <;> ring

def strong1_part_2_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 358430790) + ((d * 969620270) + (e * 496447250)))) + ((d * ((d * 1114348995) + (e * 1143307460))) + (e * (e * 399003375))))) + ((d * ((d * ((d * 602368840) + (e * 935460410))) + (e * (e * 648647330)))) + (e * (e * (e * 161777590)))))) + ((d * ((d * ((d * ((d * 123804890) + (e * 258195870))) + (e * (e * 265764240)))) + (e * (e * (e * 131373260))))) + (e * (e * (e * (e * 24595565))))))

private theorem strong1_part_2_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_4 c d e := by
  unfold strong1_part_2_4
  positivity

theorem strong1_part_2_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 4 = strong1_part_2_4 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_4 <;> ring

def strong1_part_2_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 323169180) + ((d * 649752270) + (e * 328341360)))) + ((d * ((d * 500971560) + (e * 506143740))) + (e * (e * 179560650))))) + ((d * ((d * ((d * 137551970) + (e * 210621000))) + (e * (e * 146742030)))) + (e * (e * (e * 36836500)))))

private theorem strong1_part_2_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_5 c d e := by
  unfold strong1_part_2_5
  positivity

theorem strong1_part_2_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 5 = strong1_part_2_5 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_5 <;> ring

def strong1_part_2_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * 187333105) + ((d * 249582110) + (e * 125084100)))) + ((d * ((d * 96783520) + (e * 96783520))) + (e * (e * 34534515))))

private theorem strong1_part_2_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_6 c d e := by
  unfold strong1_part_2_6
  positivity

theorem strong1_part_2_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 6 = strong1_part_2_6 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_6 <;> ring

def strong1_part_2_7 (c d e : ℝ) : ℝ :=
  ((c * 65485110) + ((d * 43656740) + (e * 21828370)))

private theorem strong1_part_2_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_7 c d e := by
  unfold strong1_part_2_7
  positivity

theorem strong1_part_2_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 7 = strong1_part_2_7 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_7 <;> ring

def strong1_part_2_8 (c d e : ℝ) : ℝ :=
  10914185

private theorem strong1_part_2_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_2_8 c d e := by
  unfold strong1_part_2_8
  positivity

theorem strong1_part_2_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 2) 8 = strong1_part_2_8 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_2_8 <;> ring

theorem strong1_coeff_2_length (c d e : ℝ) :
    (chamberPoly1 c d e 2).length ≤ 9 := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (2 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart2, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong1_coeff_2_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly1 c d e 2) b := by
  apply polyEval_nonneg_of_coeff _ b 9
    (strong1_coeff_2_length c d e) hb
  apply forall_fin9
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 0
    rw [strong1_part_2_0_eq]
    exact strong1_part_2_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 1
    rw [strong1_part_2_1_eq]
    exact strong1_part_2_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 2
    rw [strong1_part_2_2_eq]
    exact strong1_part_2_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 3
    rw [strong1_part_2_3_eq]
    exact strong1_part_2_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 4
    rw [strong1_part_2_4_eq]
    exact strong1_part_2_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 5
    rw [strong1_part_2_5_eq]
    exact strong1_part_2_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 6
    rw [strong1_part_2_6_eq]
    exact strong1_part_2_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 7
    rw [strong1_part_2_7_eq]
    exact strong1_part_2_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 2) 8
    rw [strong1_part_2_8_eq]
    exact strong1_part_2_8_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
