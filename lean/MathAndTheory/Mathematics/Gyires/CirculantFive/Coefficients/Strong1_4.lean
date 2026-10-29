module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a^4`

Generated certificate. The coefficient of `a^4` (a power of the smallest weight) in the chamber
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

def strong1_part_4_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 22986880) + ((d * 93315820) + (e * 48710360)))) + ((d * ((d * 178360800) + (e * 186702300))) + (e * (e * 64926400))))) + ((d * ((d * ((d * 192582200) + (e * 301346400))) + (e * (e * 208908200)))) + (e * (e * (e * 52703600)))))) + ((d * ((d * ((d * ((d * 119115300) + (e * 246362100))) + (e * (e * 253685800)))) + (e * (e * (e * 127465600))))) + (e * (e * (e * (e * 24205100))))))) + ((d * ((d * ((d * ((d * ((d * 39300220) + (e * 100198000))) + (e * (e * 135848100)))) + (e * (e * (e * 102140000))))) + (e * (e * (e * (e * 39128000)))))) + (e * (e * (e * (e * (e * 5969160)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 5365780) + (e * 16097340))) + (e * (e * 26895900)))) + (e * (e * (e * 26962900))))) + (e * (e * (e * (e * 15674700)))))) + (e * (e * (e * (e * (e * 4876140))))))) + (e * (e * (e * (e * (e * (e * 630520))))))))

private theorem strong1_part_4_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_4_0 c d e := by
  unfold strong1_part_4_0
  positivity

theorem strong1_part_4_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 4) 0 = strong1_part_4_0 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_4_0 <;> ring

def strong1_part_4_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 146489940) + ((d * 493878100) + (e * 254911400)))) + ((d * ((d * 768893100) + (e * 793784400))) + (e * (e * 284934800))))) + ((d * ((d * ((d * 639262200) + (e * 988587900))) + (e * (e * 699236400)))) + (e * (e * (e * 180389400)))))) + ((d * ((d * ((d * ((d * 270330300) + (e * 554870400))) + (e * (e * 577274500)))) + (e * (e * (e * 293761000))))) + (e * (e * (e * (e * 56449100))))))) + ((d * ((d * ((d * ((d * ((d * 45510860) + (e * 115724600))) + (e * (e * 157401300)))) + (e * (e * (e * 118943200))))) + (e * (e * (e * (e * 45880000)))))) + (e * (e * (e * (e * (e * 7062180)))))))

private theorem strong1_part_4_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_4_1 c d e := by
  unfold strong1_part_4_1
  positivity

theorem strong1_part_4_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 4) 1 = strong1_part_4_1 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_4_1 <;> ring

def strong1_part_4_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 384603900) + ((d * 1032294300) + (e * 527512800)))) + ((d * ((d * 1231382800) + (e * 1255667500))) + (e * (e * 469593100))))) + ((d * ((d * ((d * 703724000) + (e * 1077385800))) + (e * (e * 781362100)))) + (e * (e * (e * 206652600)))))) + ((d * ((d * ((d * ((d * 153027400) + (e * 312133100))) + (e * (e * 328660300)))) + (e * (e * (e * 169554600))))) + (e * (e * (e * (e * 32995800))))))

private theorem strong1_part_4_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_4_2 c d e := by
  unfold strong1_part_4_2
  positivity

theorem strong1_part_4_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 4) 2 = strong1_part_4_2 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_4_2 <;> ring

def strong1_part_4_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 538663900) + ((d * 1078749500) + (e * 546398800)))) + ((d * ((d * 879475900) + (e * 887210800))) + (e * (e * 347125200))))) + ((d * ((d * ((d * 260008400) + (e * 394590900))) + (e * (e * 293346300)))) + (e * (e * (e * 79381900)))))

private theorem strong1_part_4_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_4_3 c d e := by
  unfold strong1_part_4_3
  positivity

theorem strong1_part_4_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 4) 3 = strong1_part_4_3 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_4_3 <;> ring

def strong1_part_4_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * 435607200) + ((d * 579757400) + (e * 291457000)))) + ((d * ((d * 242442500) + (e * 242442500))) + (e * (e * 98292300))))

private theorem strong1_part_4_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_4_4 c d e := by
  unfold strong1_part_4_4
  positivity

theorem strong1_part_4_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 4) 4 = strong1_part_4_4 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_4_4 <;> ring

def strong1_part_4_5 (c d e : ℝ) : ℝ :=
  ((c * 202388940) + ((d * 134925960) + (e * 67462980)))

private theorem strong1_part_4_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_4_5 c d e := by
  unfold strong1_part_4_5
  positivity

theorem strong1_part_4_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 4) 5 = strong1_part_4_5 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_4_5 <;> ring

def strong1_part_4_6 (c d e : ℝ) : ℝ :=
  44975320

private theorem strong1_part_4_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_4_6 c d e := by
  unfold strong1_part_4_6
  positivity

theorem strong1_part_4_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 4) 6 = strong1_part_4_6 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_4_6 <;> ring

theorem strong1_coeff_4_length (c d e : ℝ) :
    (chamberPoly1 c d e 4).length ≤ 7 := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong1_coeff_4_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly1 c d e 4) b := by
  apply polyEval_nonneg_of_coeff _ b 7
    (strong1_coeff_4_length c d e) hb
  apply forall_fin7
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 4) 0
    rw [strong1_part_4_0_eq]
    exact strong1_part_4_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 4) 1
    rw [strong1_part_4_1_eq]
    exact strong1_part_4_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 4) 2
    rw [strong1_part_4_2_eq]
    exact strong1_part_4_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 4) 3
    rw [strong1_part_4_3_eq]
    exact strong1_part_4_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 4) 4
    rw [strong1_part_4_4_eq]
    exact strong1_part_4_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 4) 5
    rw [strong1_part_4_5_eq]
    exact strong1_part_4_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 4) 6
    rw [strong1_part_4_6_eq]
    exact strong1_part_4_6_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
