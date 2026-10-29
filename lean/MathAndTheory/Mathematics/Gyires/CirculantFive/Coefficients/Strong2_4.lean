module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a^4`

Generated certificate. The coefficient of `a^4` (a power of the smallest weight) in the chamber
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

def strong2_part_4_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 22986880) + ((d * 89210920) + (e * 44605460)))) + ((d * ((d * 166177800) + (e * 166177800))) + (e * (e * 56584900))))) + ((d * ((d * ((d * 179636000) + (e * 269454000))) + (e * (e * 184698800)))) + (e * (e * (e * 47440400)))))) + ((d * ((d * ((d * ((d * 113352300) + (e * 226704600))) + (e * (e * 231106600)))) + (e * (e * (e * 117754300))))) + (e * (e * (e * (e * 23178500))))))) + ((d * ((d * ((d * ((d * ((d * 38405320) + (e * 96013300))) + (e * (e * 129136800)))) + (e * (e * (e * 97691900))))) + (e * (e * (e * (e * 38101400)))))) + (e * (e * (e * (e * (e * 5969160)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 5365780) + (e * 16097340))) + (e * (e * 26895900)))) + (e * (e * (e * 26962900))))) + (e * (e * (e * (e * 15674700)))))) + (e * (e * (e * (e * (e * 4876140))))))) + (e * (e * (e * (e * (e * (e * 630520))))))))

private theorem strong2_part_4_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_4_0 c d e := by
  unfold strong2_part_4_0
  positivity

theorem strong2_part_4_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 4) 0 = strong2_part_4_0 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_4_0 <;> ring

def strong2_part_4_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 146489940) + ((d * 477538300) + (e * 238966700)))) + ((d * ((d * 730188600) + (e * 731952000))) + (e * (e * 260043500))))) + ((d * ((d * ((d * 609846000) + (e * 920124000))) + (e * (e * 648847200)))) + (e * (e * (e * 169521300)))))) + ((d * ((d * ((d * ((d * 263278800) + (e * 532294200))) + (e * (e * 552250000)))) + (e * (e * (e * 283234600))))) + (e * (e * (e * (e * 55422500))))))) + ((d * ((d * ((d * ((d * ((d * 45510860) + (e * 115724600))) + (e * (e * 157401300)))) + (e * (e * (e * 118943200))))) + (e * (e * (e * (e * 45880000)))))) + (e * (e * (e * (e * (e * 7062180)))))))

private theorem strong2_part_4_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_4_1 c d e := by
  unfold strong2_part_4_1
  positivity

theorem strong2_part_4_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 4) 1 = strong2_part_4_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_4_1 <;> ring

def strong2_part_4_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 384603900) + ((d * 1010902800) + (e * 504781500)))) + ((d * ((d * 1194678100) + (e * 1197863200))) + (e * (e * 445308400))))) + ((d * ((d * ((d * 688410800) + (e * 1042786200))) + (e * (e * 755997400)))) + (e * (e * (e * 201047700)))))) + ((d * ((d * ((d * ((d * 153027400) + (e * 312133100))) + (e * (e * 328660300)))) + (e * (e * (e * 169554600))))) + (e * (e * (e * (e * 32995800))))))

private theorem strong2_part_4_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_4_2 c d e := by
  unfold strong2_part_4_2
  positivity

theorem strong2_part_4_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 4) 2 = strong2_part_4_2 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_4_2 <;> ring

def strong2_part_4_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 538663900) + ((d * 1069592900) + (e * 532350700)))) + ((d * ((d * 870319300) + (e * 871741000))) + (e * (e * 339390300))))) + ((d * ((d * ((d * 260008400) + (e * 394590900))) + (e * (e * 293346300)))) + (e * (e * (e * 79381900)))))

private theorem strong2_part_4_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_4_3 c d e := by
  unfold strong2_part_4_3
  positivity

theorem strong2_part_4_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 4) 3 = strong2_part_4_3 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_4_3 <;> ring

def strong2_part_4_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * 435607200) + ((d * 579757400) + (e * 288300400)))) + ((d * ((d * 242442500) + (e * 242442500))) + (e * (e * 98292300))))

private theorem strong2_part_4_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_4_4 c d e := by
  unfold strong2_part_4_4
  positivity

theorem strong2_part_4_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 4) 4 = strong2_part_4_4 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_4_4 <;> ring

def strong2_part_4_5 (c d e : ℝ) : ℝ :=
  ((c * 202388940) + ((d * 134925960) + (e * 67462980)))

private theorem strong2_part_4_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_4_5 c d e := by
  unfold strong2_part_4_5
  positivity

theorem strong2_part_4_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 4) 5 = strong2_part_4_5 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_4_5 <;> ring

def strong2_part_4_6 (c d e : ℝ) : ℝ :=
  44975320

private theorem strong2_part_4_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_4_6 c d e := by
  unfold strong2_part_4_6
  positivity

theorem strong2_part_4_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 4) 6 = strong2_part_4_6 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_4_6 <;> ring

theorem strong2_coeff_4_length (c d e : ℝ) :
    (chamberPoly2 c d e 4).length ≤ 7 := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (4 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart4, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong2_coeff_4_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly2 c d e 4) b := by
  apply polyEval_nonneg_of_coeff _ b 7
    (strong2_coeff_4_length c d e) hb
  apply forall_fin7
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 4) 0
    rw [strong2_part_4_0_eq]
    exact strong2_part_4_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 4) 1
    rw [strong2_part_4_1_eq]
    exact strong2_part_4_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 4) 2
    rw [strong2_part_4_2_eq]
    exact strong2_part_4_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 4) 3
    rw [strong2_part_4_3_eq]
    exact strong2_part_4_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 4) 4
    rw [strong2_part_4_4_eq]
    exact strong2_part_4_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 4) 5
    rw [strong2_part_4_5_eq]
    exact strong2_part_4_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 4) 6
    rw [strong2_part_4_6_eq]
    exact strong2_part_4_6_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
