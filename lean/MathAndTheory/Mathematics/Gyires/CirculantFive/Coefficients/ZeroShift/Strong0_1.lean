module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a⁰ b^1`

Generated certificate. The coefficient of `b^1` in the constant term (in the smallest weight
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

def strong0_part_0_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 508000) + ((d * 3302840) + (e * 1358330)))) + ((d * ((d * 9933560) + (e * 7921220))) + (e * (e * 2021170))))) + ((d * ((d * ((d * 17489910) + (e * 20403010))) + (e * (e * 10725630)))) + (e * (e * (e * 2470880)))))) + ((d * ((d * ((d * ((d * 19517950) + (e * 29746040))) + (e * (e * 24373170)))) + (e * (e * (e * 11825180))))) + (e * (e * (e * (e * 2395900))))))) + ((d * ((d * ((d * ((d * ((d * 14156550) + (e * 26567710))) + (e * (e * 30621090)))) + (e * (e * (e * 23503150))))) + (e * (e * (e * (e * 9831900)))))) + (e * (e * (e * (e * (e * 1665220)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 6629910) + (e * 14870880))) + (e * (e * 23073940)))) + (e * (e * (e * 24921080))))) + (e * (e * (e * (e * 16065600)))))) + (e * (e * (e * (e * (e * 5570020))))))) + (e * (e * (e * (e * (e * (e * 811030))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1926450) + (e * 5126490))) + (e * (e * 10510410)))) + (e * (e * (e * 14912330))))) + (e * (e * (e * (e * 13099660)))))) + (e * (e * (e * (e * (e * 6957450))))))) + (e * (e * (e * (e * (e * (e * 2087960)))))))) + (e * (e * (e * (e * (e * (e * (e * 274560)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 314020) + (e * 1003660))) + (e * (e * 2690230)))) + (e * (e * (e * 4779060))))) + (e * (e * (e * (e * 5352930)))))) + (e * (e * (e * (e * (e * 3873300))))))) + (e * (e * (e * (e * (e * (e * 1791450)))))))) + (e * (e * (e * (e * (e * (e * (e * 486600))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59140))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 21680) + (e * 85780))) + (e * (e * 297770)))) + (e * (e * (e * 641610))))) + (e * (e * (e * (e * 884060)))))) + (e * (e * (e * (e * (e * 820900))))))) + (e * (e * (e * (e * (e * (e * 519320)))))))) + (e * (e * (e * (e * (e * (e * (e * 216130))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 53610)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong0_part_0_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_0_1 c d e := by
  unfold strong0_part_0_1
  positivity

theorem strong0_part_0_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 0) 1 = strong0_part_0_1 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong0_part_0_1 <;> ring

theorem strong0_part_0_1_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly0 c d e 0) 1 := by
  rw [strong0_part_0_1_eq]
  exact strong0_part_0_1_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
