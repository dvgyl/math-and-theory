module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a^5`

Generated certificate. The coefficient of `a^5` (a power of the smallest weight) in the chamber
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

def strong2_part_5_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 31011720) + ((d * 101804400) + (e * 50902200)))) + ((d * ((d * 159133200) + (e * 159133200))) + (e * (e * 58396800))))) + ((d * ((d * ((d * 136156800) + (e * 204235200))) + (e * (e * 146577600)))) + (e * (e * (e * 39249600)))))) + ((d * ((d * ((d * ((d * 59970600) + (e * 119941200))) + (e * (e * 125015400)))) + (e * (e * (e * 65044800))))) + (e * (e * (e * (e * 12897600))))))) + ((d * ((d * ((d * ((d * ((d * 10523280) + (e * 26308200))) + (e * (e * 35575200)))) + (e * (e * (e * 27054600))))) + (e * (e * (e * (e * 10526400)))))) + (e * (e * (e * (e * (e * 1631040)))))))

private theorem strong2_part_5_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_5_0 c d e := by
  unfold strong2_part_5_0
  positivity

theorem strong2_part_5_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 5) 0 = strong2_part_5_0 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_5_0 <;> ring

def strong2_part_5_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 156256800) + ((d * 412408800) + (e * 205778400)))) + ((d * ((d * 502624800) + (e * 502840800))) + (e * (e * 195883200))))) + ((d * ((d * ((d * 299596800) + (e * 451321200))) + (e * (e * 336063600)))) + (e * (e * (e * 92169600)))))) + ((d * ((d * ((d * ((d * 68392800) + (e * 138069600))) + (e * (e * 146941200)))) + (e * (e * (e * 77264400))))) + (e * (e * (e * (e * 15268800))))))

private theorem strong2_part_5_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_5_1 c d e := by
  unfold strong2_part_5_1
  positivity

theorem strong2_part_5_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 5) 1 = strong2_part_5_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_5_1 <;> ring

def strong2_part_5_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 310789800) + ((d * 618159600) + (e * 307585800)))) + ((d * ((d * 526712400) + (e * 526928400))) + (e * (e * 219342600))))) + ((d * ((d * ((d * 165163200) + (e * 249562800))) + (e * (e * 192758400)))) + (e * (e * (e * 54179400)))))

private theorem strong2_part_5_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_5_2 c d e := by
  unfold strong2_part_5_2
  positivity

theorem strong2_part_5_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 5) 2 = strong2_part_5_2 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_5_2 <;> ring

def strong2_part_5_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * 314360400) + ((d * 418435200) + (e * 208149600)))) + ((d * ((d * 187190400) + (e * 187190400))) + (e * (e * 83115600))))

private theorem strong2_part_5_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_5_3 c d e := by
  unfold strong2_part_5_3
  positivity

theorem strong2_part_5_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 5) 3 = strong2_part_5_3 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_5_3 <;> ring

def strong2_part_5_4 (c d e : ℝ) : ℝ :=
  ((c * 173433600) + ((d * 115622400) + (e * 57811200)))

private theorem strong2_part_5_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_5_4 c d e := by
  unfold strong2_part_5_4
  positivity

theorem strong2_part_5_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 5) 4 = strong2_part_5_4 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_5_4 <;> ring

def strong2_part_5_5 (c d e : ℝ) : ℝ :=
  46248960

private theorem strong2_part_5_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_5_5 c d e := by
  unfold strong2_part_5_5
  positivity

theorem strong2_part_5_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 5) 5 = strong2_part_5_5 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_5_5 <;> ring

theorem strong2_coeff_5_length (c d e : ℝ) :
    (chamberPoly2 c d e 5).length ≤ 6 := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong2_coeff_5_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly2 c d e 5) b := by
  apply polyEval_nonneg_of_coeff _ b 6
    (strong2_coeff_5_length c d e) hb
  apply forall_fin6
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 5) 0
    rw [strong2_part_5_0_eq]
    exact strong2_part_5_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 5) 1
    rw [strong2_part_5_1_eq]
    exact strong2_part_5_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 5) 2
    rw [strong2_part_5_2_eq]
    exact strong2_part_5_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 5) 3
    rw [strong2_part_5_3_eq]
    exact strong2_part_5_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 5) 4
    rw [strong2_part_5_4_eq]
    exact strong2_part_5_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly2 c d e 5) 5
    rw [strong2_part_5_5_eq]
    exact strong2_part_5_5_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
