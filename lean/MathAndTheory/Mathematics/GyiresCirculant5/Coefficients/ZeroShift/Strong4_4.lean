module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a⁰ b^4`

Generated certificate. The coefficient of `b^4` in the constant term (in the smallest weight
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

def strong4_part_0_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 15805330) + ((d * 63472320) + (e * 35524490)))) + ((d * ((d * 115382690) + (e * 131005760))) + (e * (e * 44944245))))) + ((d * ((d * ((d * 116602930) + (e * 196728190))) + (e * (e * 137202390)))) + (e * (e * (e * 34046990)))))) + ((d * ((d * ((d * ((d * 67560315) + (e * 148187030))) + (e * (e * 156078735)))) + (e * (e * (e * 78816950))))) + (e * (e * (e * (e * 14901500))))))) + ((d * ((d * ((d * ((d * ((d * 21068020) + (e * 55550150))) + (e * (e * 77957830)))) + (e * (e * (e * 60016100))))) + (e * (e * (e * (e * 23231070)))))) + (e * (e * (e * (e * (e * 3542580)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 2755260) + (e * 8265780))) + (e * (e * 14399915)))) + (e * (e * (e * 15023530))))) + (e * (e * (e * (e * 8937965)))))) + (e * (e * (e * (e * (e * 2803830))))))) + (e * (e * (e * (e * (e * (e * 360325))))))))

private theorem strong4_part_0_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_0_4 c d e := by
  unfold strong4_part_0_4
  positivity

theorem strong4_part_0_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 0) 4 = strong4_part_0_4 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong4_part_0_4 <;> ring

theorem strong4_part_0_4_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly4 c d e 0) 4 := by
  rw [strong4_part_0_4_eq]
  exact strong4_part_0_4_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
