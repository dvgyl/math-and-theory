module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a⁰ b^2`

Generated certificate. The coefficient of `b^2` in the constant term (in the smallest weight
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

def strong3_part_0_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 2609120) + ((d * 12365550) + (e * 5857950)))) + ((d * ((d * 28752625) + (e * 27287550))) + (e * (e * 7670840))))) + ((d * ((d * ((d * 41705740) + (e * 59217000))) + (e * (e * 35835180)))) + (e * (e * (e * 8495200)))))) + ((d * ((d * ((d * ((d * 40002995) + (e * 75177650))) + (e * (e * 71337540)))) + (e * (e * (e * 35429160))))) + (e * (e * (e * (e * 7103580))))))) + ((d * ((d * ((d * ((d * ((d * 25243300) + (e * 58545120))) + (e * (e * 76233930)))) + (e * (e * (e * 58581030))))) + (e * (e * (e * (e * 23904170)))))) + (e * (e * (e * (e * (e * 3982800)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 10005405) + (e * 27296730))) + (e * (e * 45474390)))) + (e * (e * (e * 47828020))))) + (e * (e * (e * (e * 29801325)))))) + (e * (e * (e * (e * (e * 10085940))))))) + (e * (e * (e * (e * (e * (e * 1447875))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2232220) + (e * 6893010))) + (e * (e * 14166060)))) + (e * (e * (e * 19184740))))) + (e * (e * (e * (e * 16262750)))))) + (e * (e * (e * (e * (e * 8397450))))))) + (e * (e * (e * (e * (e * (e * 2458260)))))))) + (e * (e * (e * (e * (e * (e * (e * 318800)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 209000) + (e * 702820))) + (e * (e * 1767465)))) + (e * (e * (e * 3000350))))) + (e * (e * (e * (e * 3262595)))))) + (e * (e * (e * (e * (e * 2290870))))))) + (e * (e * (e * (e * (e * (e * 1025450)))))))) + (e * (e * (e * (e * (e * (e * (e * 270470))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 32335))))))))))

private theorem strong3_part_0_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_0_2 c d e := by
  unfold strong3_part_0_2
  positivity

theorem strong3_part_0_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 0) 2 = strong3_part_0_2 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong3_part_0_2 <;> ring

theorem strong3_part_0_2_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly3 c d e 0) 2 := by
  rw [strong3_part_0_2_eq]
  exact strong3_part_0_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
