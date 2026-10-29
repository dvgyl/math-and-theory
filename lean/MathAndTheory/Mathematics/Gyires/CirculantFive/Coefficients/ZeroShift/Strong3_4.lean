module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a⁰ b^4`

Generated certificate. The coefficient of `b^4` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly3` is an explicit polynomial in `c`, `d`, `e` with
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

def strong3_part_0_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 15805330) + ((d * 59307490) + (e * 27947830)))) + ((d * ((d * 104401745) + (e * 98621880))) + (e * (e * 29321175))))) + ((d * ((d * ((d * 106591690) + (e * 150070640))) + (e * (e * 92820320)))) + (e * (e * (e * 23030140)))))) + ((d * ((d * ((d * ((d * 64261050) + (e * 118747990))) + (e * (e * 111570795)))) + (e * (e * (e * 56216010))))) + (e * (e * (e * (e * 11536570))))))) + ((d * ((d * ((d * ((d * ((d * 21105960) + (e * 47550600))) + (e * (e * 59447710)))) + (e * (e * (e * 45211750))))) + (e * (e * (e * (e * 18601730)))))) + (e * (e * (e * (e * (e * 3148090)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 2897340) + (e * 7557320))) + (e * (e * 11699750)))) + (e * (e * (e * 11922410))))) + (e * (e * (e * (e * 7388850)))))) + (e * (e * (e * (e * (e * 2506210))))))) + (e * (e * (e * (e * (e * (e * 360325))))))))

private theorem strong3_part_0_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_0_4 c d e := by
  unfold strong3_part_0_4
  positivity

theorem strong3_part_0_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 0) 4 = strong3_part_0_4 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong3_part_0_4 <;> ring

theorem strong3_part_0_4_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly3 c d e 0) 4 := by
  rw [strong3_part_0_4_eq]
  exact strong3_part_0_4_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
