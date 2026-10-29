module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a⁰ b^5`

Generated certificate. The coefficient of `b^5` in the constant term (in the smallest weight
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

def strong3_part_0_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 21700744) + ((d * 69464620) + (e * 33051890)))) + ((d * ((d * 100302450) + (e * 95657040))) + (e * (e * 29314180))))) + ((d * ((d * ((d * 78607730) + (e * 111444150))) + (e * (e * 69871800)))) + (e * (e * (e * 17627190)))))) + ((d * ((d * ((d * ((d * 32233340) + (e * 59723580))) + (e * (e * 56012190)))) + (e * (e * (e * 28291440))))) + (e * (e * (e * (e * 5828340))))))) + ((d * ((d * ((d * ((d * ((d * 5386816) + (e * 12111140))) + (e * (e * 14898050)))) + (e * (e * (e * 11220770))))) + (e * (e * (e * (e * 4601780)))))) + (e * (e * (e * (e * (e * 777368)))))))

private theorem strong3_part_0_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_0_5 c d e := by
  unfold strong3_part_0_5
  positivity

theorem strong3_part_0_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 0) 5 = strong3_part_0_5 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong3_part_0_5 <;> ring

theorem strong3_part_0_5_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly3 c d e 0) 5 := by
  rw [strong3_part_0_5_eq]
  exact strong3_part_0_5_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
