module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a⁰ b^3`

Generated certificate. The coefficient of `b^3` in the constant term (in the smallest weight
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

def strong3_part_0_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 7923830) + ((d * 33798440) + (e * 15892700)))) + ((d * ((d * 69420720) + (e * 65421320))) + (e * (e * 18886520))))) + ((d * ((d * ((d * 86306770) + (e * 121479280))) + (e * (e * 74217120)))) + (e * (e * (e * 18030760)))))) + ((d * ((d * ((d * ((d * 67834180) + (e * 125853840))) + (e * (e * 118684070)))) + (e * (e * (e * 59457040))))) + (e * (e * (e * (e * 12088710))))))) + ((d * ((d * ((d * ((d * ((d * 32769840) + (e * 74552610))) + (e * (e * 95016380)))) + (e * (e * (e * 72758550))))) + (e * (e * (e * (e * 29883270)))))) + (e * (e * (e * (e * (e * 5034340)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 8827340) + (e * 23409720))) + (e * (e * 37567900)))) + (e * (e * (e * 38990960))))) + (e * (e * (e * (e * 24286190)))))) + (e * (e * (e * (e * (e * 8248780))))))) + (e * (e * (e * (e * (e * (e * 1189760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1006480) + (e * 2979860))) + (e * (e * 5787160)))) + (e * (e * (e * 7676470))))) + (e * (e * (e * (e * 6473850)))))) + (e * (e * (e * (e * (e * 3332270))))))) + (e * (e * (e * (e * (e * (e * 970190)))))))) + (e * (e * (e * (e * (e * (e * (e * 124540)))))))))

private theorem strong3_part_0_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_0_3 c d e := by
  unfold strong3_part_0_3
  positivity

theorem strong3_part_0_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 0) 3 = strong3_part_0_3 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong3_part_0_3 <;> ring

theorem strong3_part_0_3_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly3 c d e 0) 3 := by
  rw [strong3_part_0_3_eq]
  exact strong3_part_0_3_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
