module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a⁰ b^2`

Generated certificate. The coefficient of `b^2` in the constant term (in the smallest weight
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

def strong2_part_0_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 2609120) + ((d * 12365550) + (e * 6507600)))) + ((d * ((d * 28752625) + (e * 30217700))) + (e * (e * 9135915))))) + ((d * ((d * ((d * 41705740) + (e * 65900220))) + (e * (e * 42518400)))) + (e * (e * (e * 9828720)))))) + ((d * ((d * ((d * ((d * 40002995) + (e * 84834330))) + (e * (e * 85822560)))) + (e * (e * (e * 41724950))))) + (e * (e * (e * (e * 7837305))))))) + ((d * ((d * ((d * ((d * ((d * 25243300) + (e * 67671380))) + (e * (e * 94486450)))) + (e * (e * (e * 71283040))))) + (e * (e * (e * (e * 27479920)))))) + (e * (e * (e * (e * (e * 4272450)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 10005405) + (e * 32735700))) + (e * (e * 59071815)))) + (e * (e * (e * 61210340))))) + (e * (e * (e * (e * 36277380)))))) + (e * (e * (e * (e * (e * 11478990))))))) + (e * (e * (e * (e * (e * (e * 1518305))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2232220) + (e * 8732530))) + (e * (e * 19684620)))) + (e * (e * (e * 26378110))))) + (e * (e * (e * (e * 21451890)))))) + (e * (e * (e * (e * (e * 10424430))))))) + (e * (e * (e * (e * (e * (e * 2810430)))))))) + (e * (e * (e * (e * (e * (e * (e * 325290)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 209000) + (e * 969180))) + (e * (e * 2699725)))) + (e * (e * (e * 4549220))))) + (e * (e * (e * (e * 4804120)))))) + (e * (e * (e * (e * (e * 3210610))))))) + (e * (e * (e * (e * (e * (e * 1329665)))))))) + (e * (e * (e * (e * (e * (e * (e * 313500))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 32335))))))))))

private theorem strong2_part_0_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_0_2 c d e := by
  unfold strong2_part_0_2
  positivity

theorem strong2_part_0_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 0) 2 = strong2_part_0_2 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong2_part_0_2 <;> ring

theorem strong2_part_0_2_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly2 c d e 0) 2 := by
  rw [strong2_part_0_2_eq]
  exact strong2_part_0_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
