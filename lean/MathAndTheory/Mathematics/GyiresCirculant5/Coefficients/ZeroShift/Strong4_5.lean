module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a⁰ b^5`

Generated certificate. The coefficient of `b^5` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly4` is an explicit polynomial in `c`, `d`, `e` with
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

def strong4_part_0_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 21700744) + ((d * 72090990) + (e * 39039100)))) + ((d * ((d * 105316110) + (e * 115453340))) + (e * (e * 39451410))))) + ((d * ((d * ((d * 81001640) + (e * 131197500))) + (e * (e * 90342390)))) + (e * (e * (e * 22519340)))))) + ((d * ((d * ((d * ((d * 31974040) + (e * 66870560))) + (e * (e * 68837430)))) + (e * (e * (e * 34683040))))) + (e * (e * (e * (e * 6570470))))))) + ((d * ((d * ((d * ((d * ((d * 5120896) + (e * 12802240))) + (e * (e * 17359120)))) + (e * (e * (e * 13236440))))) + (e * (e * (e * (e * 5113400)))))) + (e * (e * (e * (e * (e * 777368)))))))

private theorem strong4_part_0_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_0_5 c d e := by
  unfold strong4_part_0_5
  positivity

theorem strong4_part_0_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 0) 5 = strong4_part_0_5 c d e := by
  dsimp only [chamberPoly4, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift4_0_eq, compactShift4_1_eq, compactShift4_2_eq,
    compactShift4_3_eq, compactShift4_4_eq, compactShift4_5_eq,
    compactGram4_0_eq, compactGram4_1_eq, compactGram4_2_eq]
  dsimp only [compactShift4_0, compactShift4_1, compactShift4_2,
    compactShift4_3, compactShift4_4, compactShift4_5,
    compactGram4_0, compactGram4_1, compactGram4_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly4, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong4_part_0_5 <;> ring

theorem strong4_part_0_5_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly4 c d e 0) 5 := by
  rw [strong4_part_0_5_eq]
  exact strong4_part_0_5_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
