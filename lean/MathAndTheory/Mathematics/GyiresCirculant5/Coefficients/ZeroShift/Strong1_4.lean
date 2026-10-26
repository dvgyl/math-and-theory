module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a⁰ b^4`

Generated certificate. The coefficient of `b^4` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly1` is an explicit polynomial in `c`, `d`, `e` with
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

def strong1_part_0_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 15805330) + ((d * 66884150) + (e * 35524490)))) + ((d * ((d * 126661975) + (e * 136505180))) + (e * (e * 44944245))))) + ((d * ((d * ((d * 130882860) + (e * 215240200))) + (e * (e * 144715560)))) + (e * (e * (e * 34046990)))))) + ((d * ((d * ((d * ((d * 75974850) + (e * 169060010))) + (e * (e * 173518095)))) + (e * (e * (e * 82930020))))) + (e * (e * (e * (e * 14901500))))))) + ((d * ((d * ((d * ((d * ((d * 23212160) + (e * 65269100))) + (e * (e * 90796340)))) + (e * (e * (e * 66236690))))) + (e * (e * (e * (e * 24284830)))))) + (e * (e * (e * (e * (e * 3542580)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 2897340) + (e * 9826720))) + (e * (e * 17373250)))) + (e * (e * (e * 17250190))))) + (e * (e * (e * (e * 9707020)))))) + (e * (e * (e * (e * (e * 2900700))))))) + (e * (e * (e * (e * (e * (e * 360325))))))))

private theorem strong1_part_0_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_0_4 c d e := by
  unfold strong1_part_0_4
  positivity

theorem strong1_part_0_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 0) 4 = strong1_part_0_4 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_0_4 <;> ring

theorem strong1_part_0_4_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly1 c d e 0) 4 := by
  rw [strong1_part_0_4_eq]
  exact strong1_part_0_4_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
