module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a⁰ b^3`

Generated certificate. The coefficient of `b^3` in the constant term (in the smallest weight
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

def strong5_part_0_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 7923830) + ((d * 37561070) + (e * 15892700)))) + ((d * ((d * 81851910) + (e * 67707920))) + (e * (e * 18886520))))) + ((d * ((d * ((d * 102163700) + (e * 127286420))) + (e * (e * 74307760)))) + (e * (e * (e * 18030760)))))) + ((d * ((d * ((d * ((d * 77319130) + (e * 131418500))) + (e * (e * 121211050)))) + (e * (e * (e * 61020840))))) + (e * (e * (e * (e * 12088710))))))) + ((d * ((d * ((d * ((d * ((d * 35154680) + (e * 77659800))) + (e * (e * 100954840)))) + (e * (e * (e * 78446830))))) + (e * (e * (e * (e * 31554560)))))) + (e * (e * (e * (e * (e * 5034340)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 8868560) + (e * 24819000))) + (e * (e * 42745730)))) + (e * (e * (e * 45415380))))) + (e * (e * (e * (e * 27731680)))))) + (e * (e * (e * (e * (e * 8958460))))))) + (e * (e * (e * (e * (e * (e * 1189760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 959440) + (e * 3358040))) + (e * (e * 7365040)))) + (e * (e * (e * 10017500))))) + (e * (e * (e * (e * 8259380)))))) + (e * (e * (e * (e * (e * 4050590))))))) + (e * (e * (e * (e * (e * (e * 1091350)))))))) + (e * (e * (e * (e * (e * (e * (e * 124540)))))))))

private theorem strong5_part_0_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_0_3 c d e := by
  unfold strong5_part_0_3
  positivity

theorem strong5_part_0_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 0) 3 = strong5_part_0_3 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong5_part_0_3 <;> ring

theorem strong5_part_0_3_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly5 c d e 0) 3 := by
  rw [strong5_part_0_3_eq]
  exact strong5_part_0_3_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
