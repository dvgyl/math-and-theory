module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a^5`

Generated certificate. The coefficient of `a^5` (a power of the smallest weight) in the chamber
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

def strong3_part_5_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 31011720) + ((d * 101804400) + (e * 50902200)))) + ((d * ((d * 159133200) + (e * 159133200))) + (e * (e * 58396800))))) + ((d * ((d * ((d * 136156800) + (e * 204235200))) + (e * (e * 146577600)))) + (e * (e * (e * 39249600)))))) + ((d * ((d * ((d * ((d * 59970600) + (e * 119941200))) + (e * (e * 125015400)))) + (e * (e * (e * 65044800))))) + (e * (e * (e * (e * 12897600))))))) + ((d * ((d * ((d * ((d * ((d * 10523280) + (e * 26308200))) + (e * (e * 35575200)))) + (e * (e * (e * 27054600))))) + (e * (e * (e * (e * 10526400)))))) + (e * (e * (e * (e * (e * 1631040)))))))

private theorem strong3_part_5_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_5_0 c d e := by
  unfold strong3_part_5_0
  positivity

theorem strong3_part_5_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 5) 0 = strong3_part_5_0 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_5_0 <;> ring

def strong3_part_5_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 156256800) + ((d * 412408800) + (e * 206630400)))) + ((d * ((d * 502624800) + (e * 502408800))) + (e * (e * 195667200))))) + ((d * ((d * ((d * 299596800) + (e * 447469200))) + (e * (e * 332211600)))) + (e * (e * (e * 92169600)))))) + ((d * ((d * ((d * ((d * 68392800) + (e * 135501600))) + (e * (e * 143089200)))) + (e * (e * (e * 75980400))))) + (e * (e * (e * (e * 15268800))))))

private theorem strong3_part_5_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_5_1 c d e := by
  unfold strong3_part_5_1
  positivity

theorem strong3_part_5_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 5) 1 = strong3_part_5_1 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_5_1 <;> ring

def strong3_part_5_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 310789800) + ((d * 618159600) + (e * 310573800)))) + ((d * ((d * 526712400) + (e * 526496400))) + (e * (e * 219126600))))) + ((d * ((d * ((d * 165163200) + (e * 245926800))) + (e * (e * 189122400)))) + (e * (e * (e * 54179400)))))

private theorem strong3_part_5_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_5_2 c d e := by
  unfold strong3_part_5_2
  positivity

theorem strong3_part_5_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 5) 2 = strong3_part_5_2 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_5_2 <;> ring

def strong3_part_5_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * 314360400) + ((d * 418435200) + (e * 210285600)))) + ((d * ((d * 187190400) + (e * 187190400))) + (e * (e * 83115600))))

private theorem strong3_part_5_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_5_3 c d e := by
  unfold strong3_part_5_3
  positivity

theorem strong3_part_5_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 5) 3 = strong3_part_5_3 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_5_3 <;> ring

def strong3_part_5_4 (c d e : ℝ) : ℝ :=
  ((c * 173433600) + ((d * 115622400) + (e * 57811200)))

private theorem strong3_part_5_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_5_4 c d e := by
  unfold strong3_part_5_4
  positivity

theorem strong3_part_5_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 5) 4 = strong3_part_5_4 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_5_4 <;> ring

def strong3_part_5_5 (c d e : ℝ) : ℝ :=
  46248960

private theorem strong3_part_5_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_5_5 c d e := by
  unfold strong3_part_5_5
  positivity

theorem strong3_part_5_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 5) 5 = strong3_part_5_5 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_5_5 <;> ring

theorem strong3_coeff_5_length (c d e : ℝ) :
    (chamberPoly3 c d e 5).length ≤ 6 := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_right (show (5 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart5, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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

theorem strong3_coeff_5_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly3 c d e 5) b := by
  apply polyEval_nonneg_of_coeff _ b 6
    (strong3_coeff_5_length c d e) hb
  apply forall_fin6
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 5) 0
    rw [strong3_part_5_0_eq]
    exact strong3_part_5_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 5) 1
    rw [strong3_part_5_1_eq]
    exact strong3_part_5_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 5) 2
    rw [strong3_part_5_2_eq]
    exact strong3_part_5_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 5) 3
    rw [strong3_part_5_3_eq]
    exact strong3_part_5_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 5) 4
    rw [strong3_part_5_4_eq]
    exact strong3_part_5_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly3 c d e 5) 5
    rw [strong3_part_5_5_eq]
    exact strong3_part_5_5_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
