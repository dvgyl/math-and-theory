module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a⁰ b^1`

Generated certificate. The coefficient of `b^1` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly2` is an explicit polynomial in `c`, `d`, `e` with
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

def strong2_part_0_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 508000) + ((d * 2627490) + (e * 1358330)))) + ((d * ((d * 6765430) + (e * 6987760))) + (e * (e * 2021170))))) + ((d * ((d * ((d * 11118640) + (e * 17245470))) + (e * (e * 10835200)))) + (e * (e * (e * 2470880)))))) + ((d * ((d * ((d * ((d * 12485050) + (e * 25904700))) + (e * (e * 25839660)))) + (e * (e * (e * 12583700))))) + (e * (e * (e * (e * 2395900))))))) + ((d * ((d * ((d * ((d * ((d * 9645940) + (e * 25163430))) + (e * (e * 34960410)))) + (e * (e * (e * 26683050))))) + (e * (e * (e * (e * 10473700)))))) + (e * (e * (e * (e * (e * 1665220)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 5001950) + (e * 15803240))) + (e * (e * 28577640)))) + (e * (e * (e * 30174520))))) + (e * (e * (e * (e * 18316750)))))) + (e * (e * (e * (e * (e * 5957040))))))) + (e * (e * (e * (e * (e * (e * 811030))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1639770) + (e * 6129240))) + (e * (e * 13933110)))) + (e * (e * (e * 19137650))))) + (e * (e * (e * (e * 16044840)))))) + (e * (e * (e * (e * (e * 8075250))))))) + (e * (e * (e * (e * (e * (e * 2267050)))))))) + (e * (e * (e * (e * (e * (e * (e * 274560)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 299100) + (e * 1304580))) + (e * (e * 3686350)))) + (e * (e * (e * 6400220))))) + (e * (e * (e * (e * 7021710)))))) + (e * (e * (e * (e * (e * 4908900))))))) + (e * (e * (e * (e * (e * (e * 2142180)))))))) + (e * (e * (e * (e * (e * (e * (e * 535640))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59140))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 21680) + (e * 109340))) + (e * (e * 392010)))) + (e * (e * (e * 862060))))) + (e * (e * (e * (e * 1215570)))))) + (e * (e * (e * (e * (e * 1124280))))))) + (e * (e * (e * (e * (e * (e * 683510)))))))) + (e * (e * (e * (e * (e * (e * (e * 264690))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong2_part_0_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_0_1 c d e := by
  unfold strong2_part_0_1
  positivity

theorem strong2_part_0_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 0) 1 = strong2_part_0_1 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
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
  norm_num [polyCoeff] <;> unfold strong2_part_0_1 <;> ring

theorem strong2_part_0_1_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly2 c d e 0) 1 := by
  rw [strong2_part_0_1_eq]
  exact strong2_part_0_1_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
