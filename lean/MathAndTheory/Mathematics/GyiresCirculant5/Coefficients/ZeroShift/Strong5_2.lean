module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a⁰ b^2`

Generated certificate. The coefficient of `b^2` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly5` is an explicit polynomial in `c`, `d`, `e` with
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

def strong5_part_0_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 2609120) + ((d * 14365360) + (e * 5857950)))) + ((d * ((d * 36638075) + (e * 29059780))) + (e * (e * 7670840))))) + ((d * ((d * ((d * 54437890) + (e * 64373970))) + (e * (e * 35675460)))) + (e * (e * (e * 8495200)))))) + ((d * ((d * ((d * ((d * 50604830) + (e * 80625670))) + (e * (e * 70986240)))) + (e * (e * (e * 35461160))))) + (e * (e * (e * (e * 7103580))))))) + ((d * ((d * ((d * ((d * ((d * 29852590) + (e * 61048000))) + (e * (e * 76519300)))) + (e * (e * (e * 59684990))))) + (e * (e * (e * (e * 24424150)))))) + (e * (e * (e * (e * (e * 3982800)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 10872070) + (e * 27880770))) + (e * (e * 46989465)))) + (e * (e * (e * 50715390))))) + (e * (e * (e * (e * 31740720)))))) + (e * (e * (e * (e * (e * 10549710))))))) + (e * (e * (e * (e * (e * (e * 1447875))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2234840) + (e * 7136800))) + (e * (e * 15620790)))) + (e * (e * (e * 21845490))))) + (e * (e * (e * (e * 18631910)))))) + (e * (e * (e * (e * (e * 9493710))))))) + (e * (e * (e * (e * (e * (e * 2669090)))))))) + (e * (e * (e * (e * (e * (e * (e * 318800)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 198920) + (e * 795680))) + (e * (e * 2209550)))) + (e * (e * (e * 3843770))))) + (e * (e * (e * (e * 4198755)))))) + (e * (e * (e * (e * (e * 2919520))))))) + (e * (e * (e * (e * (e * (e * 1258755)))))))) + (e * (e * (e * (e * (e * (e * (e * 307010))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 32335))))))))))

private theorem strong5_part_0_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_0_2 c d e := by
  unfold strong5_part_0_2
  positivity

theorem strong5_part_0_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 0) 2 = strong5_part_0_2 c d e := by
  dsimp only [chamberPoly5, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift5_0_eq, compactShift5_1_eq, compactShift5_2_eq,
    compactShift5_3_eq, compactShift5_4_eq, compactShift5_5_eq,
    compactGram5_0_eq, compactGram5_1_eq, compactGram5_2_eq]
  dsimp only [compactShift5_0, compactShift5_1, compactShift5_2,
    compactShift5_3, compactShift5_4, compactShift5_5,
    compactGram5_0, compactGram5_1, compactGram5_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly5, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong5_part_0_2 <;> ring

theorem strong5_part_0_2_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly5 c d e 0) 2 := by
  rw [strong5_part_0_2_eq]
  exact strong5_part_0_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
