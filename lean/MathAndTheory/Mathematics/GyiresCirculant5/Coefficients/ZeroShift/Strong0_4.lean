module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a⁰ b^4`

Generated certificate. The coefficient of `b^4` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly0` is an explicit polynomial in `c`, `d`, `e` with
nonnegative integer coefficients; it is proved equal to the computed coefficient by `ring` and
nonnegative for `c, d, e ≥ 0` by `positivity`.
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

def strong0_part_0_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 15805330) + ((d * 66884150) + (e * 31359660)))) + ((d * ((d * 126661975) + (e * 116818770))) + (e * (e * 35101040))))) + ((d * ((d * ((d * 130882860) + (e * 177408380))) + (e * (e * 106883740)))) + (e * (e * (e * 26311230)))))) + ((d * ((d * ((d * ((d * 75974850) + (e * 134839390))) + (e * (e * 122187165)))) + (e * (e * (e * 60825540))))) + (e * (e * (e * (e * 12404415))))))) + ((d * ((d * ((d * ((d * ((d * 23212160) + (e * 50791700))) + (e * (e * 61841540)))) + (e * (e * (e * 46659330))))) + (e * (e * (e * (e * 19184870)))))) + (e * (e * (e * (e * (e * 3244960)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 2897340) + (e * 7557320))) + (e * (e * 11699750)))) + (e * (e * (e * 11922410))))) + (e * (e * (e * (e * 7388850)))))) + (e * (e * (e * (e * (e * 2506210))))))) + (e * (e * (e * (e * (e * (e * 360325))))))))

private theorem strong0_part_0_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_0_4 c d e := by
  unfold strong0_part_0_4
  positivity

theorem strong0_part_0_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 0) 4 = strong0_part_0_4 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_0_4 <;> ring

theorem strong0_part_0_4_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly0 c d e 0) 4 := by
  rw [strong0_part_0_4_eq]
  exact strong0_part_0_4_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
