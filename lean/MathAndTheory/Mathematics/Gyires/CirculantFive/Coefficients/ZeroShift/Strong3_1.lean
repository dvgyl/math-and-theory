module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a⁰ b^1`

Generated certificate. The coefficient of `b^1` in the constant term (in the smallest weight
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

def strong3_part_0_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 508000) + ((d * 2627490) + (e * 1269160)))) + ((d * ((d * 6765430) + (e * 6543100))) + (e * (e * 1798840))))) + ((d * ((d * ((d * 11118640) + (e * 16110450))) + (e * (e * 9700180)))) + (e * (e * (e * 2237490)))))) + ((d * ((d * ((d * ((d * 12485050) + (e * 24035500))) + (e * (e * 23035860)))) + (e * (e * (e * 11321720))))) + (e * (e * (e * (e * 2232210))))))) + ((d * ((d * ((d * ((d * ((d * 9645940) + (e * 23066270))) + (e * (e * 30766090)))) + (e * (e * (e * 23677000))))) + (e * (e * (e * (e * 9564810)))))) + (e * (e * (e * (e * (e * 1568350)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 5001950) + (e * 14208460))) + (e * (e * 24590690)))) + (e * (e * (e * 26142640))))) + (e * (e * (e * (e * 16255880)))))) + (e * (e * (e * (e * (e * 5458960))))))) + (e * (e * (e * (e * (e * (e * 772570))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1639770) + (e * 5349150))) + (e * (e * 11592840)))) + (e * (e * (e * 15981250))))) + (e * (e * (e * (e * 13632490)))))) + (e * (e * (e * (e * (e * 7061040))))))) + (e * (e * (e * (e * (e * (e * 2068970)))))))) + (e * (e * (e * (e * (e * (e * (e * 268070)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 299100) + (e * 1088220))) + (e * (e * 2929090)))) + (e * (e * (e * 5071300))))) + (e * (e * (e * (e * 5592560)))))) + (e * (e * (e * (e * (e * 3992040))))))) + (e * (e * (e * (e * (e * (e * 1817410)))))))) + (e * (e * (e * (e * (e * (e * (e * 486600))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59140))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 21680) + (e * 85780))) + (e * (e * 297770)))) + (e * (e * (e * 641610))))) + (e * (e * (e * (e * 884060)))))) + (e * (e * (e * (e * (e * 820900))))))) + (e * (e * (e * (e * (e * (e * 519320)))))))) + (e * (e * (e * (e * (e * (e * (e * 216130))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 53610)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong3_part_0_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_0_1 c d e := by
  unfold strong3_part_0_1
  positivity

theorem strong3_part_0_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 0) 1 = strong3_part_0_1 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong3_part_0_1 <;> ring

theorem strong3_part_0_1_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly3 c d e 0) 1 := by
  rw [strong3_part_0_1_eq]
  exact strong3_part_0_1_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
