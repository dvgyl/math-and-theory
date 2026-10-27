module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a⁰ b^0`

Generated certificate. The coefficient of `b^0` in the constant term (in the smallest weight
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

def strong4_part_0_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 43725) + ((d * 319170) + (e * 196250)))) + ((d * ((d * 1069675) + (e * 1349160))) + (e * (e * 466035))))) + ((d * ((d * ((d * 2118060) + (e * 4083920))) + (e * (e * 2932200)))) + (e * (e * (e * 712040)))))) + ((d * ((d * ((d * ((d * 2696065) + (e * 7036510))) + (e * (e * 7868285)))) + (e * (e * (e * 3975230))))) + (e * (e * (e * (e * 741545))))))) + ((d * ((d * ((d * ((d * ((d * 2276212) + (e * 7508220))) + (e * (e * 11657310)))) + (e * (e * (e * 9226830))))) + (e * (e * (e * (e * 3599400)))))) + (e * (e * (e * (e * (e * 549906)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 1279875) + (e * 5087430))) + (e * (e * 10332080)))) + (e * (e * (e * 11449060))))) + (e * (e * (e * (e * 7044880)))))) + (e * (e * (e * (e * (e * 2263020))))))) + (e * (e * (e * (e * (e * (e * 296085))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 469370) + (e * 2160740))) + (e * (e * 5552320)))) + (e * (e * (e * 8129870))))) + (e * (e * (e * (e * 7066910)))))) + (e * (e * (e * (e * (e * 3607250))))))) + (e * (e * (e * (e * (e * (e * 999430)))))))) + (e * (e * (e * (e * (e * (e * (e * 116360)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 105645) + (e * 541820))) + (e * (e * 1741995)))) + (e * (e * (e * 3266260))))) + (e * (e * (e * (e * 3793445)))))) + (e * (e * (e * (e * (e * 2759950))))))) + (e * (e * (e * (e * (e * (e * 1225775)))))))) + (e * (e * (e * (e * (e * (e * (e * 304840))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 32575))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 12540) + (e * 68210))) + (e * (e * 283790)))) + (e * (e * (e * 675230))))) + (e * (e * (e * (e * 1018180)))))) + (e * (e * (e * (e * (e * 1001910))))))) + (e * (e * (e * (e * (e * (e * 641920)))))))) + (e * (e * (e * (e * (e * (e * (e * 258680))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * (e * 2420)) + (e * (e * 16985)))) + (e * (e * (e * 53420))))) + (e * (e * (e * (e * 103900)))))) + (e * (e * (e * (e * (e * 134894))))))) + (e * (e * (e * (e * (e * (e * 118770)))))))) + (e * (e * (e * (e * (e * (e * (e * 70200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 26805)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010))))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * (e * 117))))))))))))

private theorem strong4_part_0_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_0_0 c d e := by
  unfold strong4_part_0_0
  positivity

theorem strong4_part_0_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 0) 0 = strong4_part_0_0 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong4_part_0_0 <;> ring

theorem strong4_part_0_0_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly4 c d e 0) 0 := by
  rw [strong4_part_0_0_eq]
  exact strong4_part_0_0_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
