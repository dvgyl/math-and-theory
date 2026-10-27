module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a^5`

Generated certificate. The coefficient of `a^5` (a power of the smallest weight) in the chamber
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

def strong1_part_5_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 31011720) + ((d * 104156400) + (e * 53254200)))) + ((d * ((d * 164905200) + (e * 168541200))) + (e * (e * 62032800))))) + ((d * ((d * ((d * 140644800) + (e * 214711200))) + (e * (e * 153849600)))) + (e * (e * (e * 40533600)))))) + ((d * ((d * ((d * ((d * 61038600) + (e * 123361200))) + (e * (e * 128651400)))) + (e * (e * (e * 66328800))))) + (e * (e * (e * (e * 12897600))))))) + ((d * ((d * ((d * ((d * ((d * 10523280) + (e * 26308200))) + (e * (e * 35575200)))) + (e * (e * (e * 27054600))))) + (e * (e * (e * (e * 10526400)))))) + (e * (e * (e * (e * (e * 1631040)))))))

private theorem strong1_part_5_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_5_0 c d e := by
  unfold strong1_part_5_0
  positivity

theorem strong1_part_5_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 5) 0 = strong1_part_5_0 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_5_0 <;> ring

def strong1_part_5_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 156256800) + ((d * 418396800) + (e * 212618400)))) + ((d * ((d * 513316800) + (e * 520372800))) + (e * (e * 202939200))))) + ((d * ((d * ((d * 304300800) + (e * 462013200))) + (e * (e * 343335600)))) + (e * (e * (e * 93453600)))))) + ((d * ((d * ((d * ((d * 68392800) + (e * 138069600))) + (e * (e * 146941200)))) + (e * (e * (e * 77264400))))) + (e * (e * (e * (e * 15268800))))))

private theorem strong1_part_5_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_5_1 c d e := by
  unfold strong1_part_5_1
  positivity

theorem strong1_part_5_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 5) 1 = strong1_part_5_1 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_5_1 <;> ring

def strong1_part_5_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 310789800) + ((d * 621795600) + (e * 314209800)))) + ((d * ((d * 530348400) + (e * 533768400))) + (e * (e * 222762600))))) + ((d * ((d * ((d * 165163200) + (e * 249562800))) + (e * (e * 192758400)))) + (e * (e * (e * 54179400)))))

private theorem strong1_part_5_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_5_2 c d e := by
  unfold strong1_part_5_2
  positivity

theorem strong1_part_5_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 5) 2 = strong1_part_5_2 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_5_2 <;> ring

def strong1_part_5_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * 314360400) + ((d * 418435200) + (e * 210285600)))) + ((d * ((d * 187190400) + (e * 187190400))) + (e * (e * 83115600))))

private theorem strong1_part_5_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_5_3 c d e := by
  unfold strong1_part_5_3
  positivity

theorem strong1_part_5_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 5) 3 = strong1_part_5_3 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_5_3 <;> ring

def strong1_part_5_4 (c d e : ℝ) : ℝ :=
  ((c * 173433600) + ((d * 115622400) + (e * 57811200)))

private theorem strong1_part_5_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_5_4 c d e := by
  unfold strong1_part_5_4
  positivity

theorem strong1_part_5_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 5) 4 = strong1_part_5_4 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_5_4 <;> ring

def strong1_part_5_5 (c d e : ℝ) : ℝ :=
  46248960

private theorem strong1_part_5_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_5_5 c d e := by
  unfold strong1_part_5_5
  positivity

theorem strong1_part_5_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 5) 5 = strong1_part_5_5 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong1_part_5_5 <;> ring

theorem strong1_coeff_5_length (c d e : ℝ) :
    (chamberPoly1 c d e 5).length ≤ 6 := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong1_coeff_5_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly1 c d e 5) b := by
  apply polyEval_nonneg_of_coeff _ b 6
    (strong1_coeff_5_length c d e) hb
  apply forall_fin6
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 5) 0
    rw [strong1_part_5_0_eq]
    exact strong1_part_5_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 5) 1
    rw [strong1_part_5_1_eq]
    exact strong1_part_5_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 5) 2
    rw [strong1_part_5_2_eq]
    exact strong1_part_5_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 5) 3
    rw [strong1_part_5_3_eq]
    exact strong1_part_5_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 5) 4
    rw [strong1_part_5_4_eq]
    exact strong1_part_5_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 5) 5
    rw [strong1_part_5_5_eq]
    exact strong1_part_5_5_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
