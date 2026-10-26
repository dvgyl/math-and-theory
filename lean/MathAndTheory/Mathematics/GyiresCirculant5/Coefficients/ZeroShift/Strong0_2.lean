module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a⁰ b^2`

Generated certificate. The coefficient of `b^2` in the constant term (in the smallest weight
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

def strong0_part_0_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 2609120) + ((d * 15015010) + (e * 6507600)))) + ((d * ((d * 39720550) + (e * 33607330))) + (e * (e * 9135915))))) + ((d * ((d * ((d * 60623610) + (e * 75333960))) + (e * (e * 41783250)))) + (e * (e * (e * 9828720)))))) + ((d * ((d * ((d * ((d * 57300330) + (e * 93311010))) + (e * (e * 79549065)))) + (e * (e * (e * 38767870))))) + (e * (e * (e * (e * 7837305))))))) + ((d * ((d * ((d * ((d * ((d * 33978790) + (e * 68275210))) + (e * (e * 80289710)))) + (e * (e * (e * 60872140))))) + (e * (e * (e * (e * 25231550)))))) + (e * (e * (e * (e * (e * 4272450)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 12269965) + (e * 29450130))) + (e * (e * 45458265)))) + (e * (e * (e * 47771780))))) + (e * (e * (e * (e * 30327825)))))) + (e * (e * (e * (e * (e * 10448190))))))) + (e * (e * (e * (e * (e * (e * 1518305))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2459220) + (e * 6966310))) + (e * (e * 13800210)))) + (e * (e * (e * 18846420))))) + (e * (e * (e * (e * 16209180)))))) + (e * (e * (e * (e * (e * 8471970))))))) + (e * (e * (e * (e * (e * (e * 2503210)))))))) + (e * (e * (e * (e * (e * (e * (e * 325290)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 209000) + (e * 702820))) + (e * (e * 1767465)))) + (e * (e * (e * 3000350))))) + (e * (e * (e * (e * 3262595)))))) + (e * (e * (e * (e * (e * 2290870))))))) + (e * (e * (e * (e * (e * (e * 1025450)))))))) + (e * (e * (e * (e * (e * (e * (e * 270470))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 32335))))))))))

private theorem strong0_part_0_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_0_2 c d e := by
  unfold strong0_part_0_2
  positivity

theorem strong0_part_0_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 0) 2 = strong0_part_0_2 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong0_part_0_2 <;> ring

theorem strong0_part_0_2_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly0 c d e 0) 2 := by
  rw [strong0_part_0_2_eq]
  exact strong0_part_0_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
