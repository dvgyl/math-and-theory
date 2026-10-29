module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a⁰ b^0`

Generated certificate. The coefficient of `b^0` in the constant term (in the smallest weight
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

def strong0_part_0_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 43725) + ((d * 319170) + (e * 122920)))) + ((d * ((d * 1069675) + (e * 790190))) + (e * (e * 186550))))) + ((d * ((d * ((d * 2118060) + (e * 2270260))) + (e * (e * 1118540)))) + (e * (e * (e * 254300)))))) + ((d * ((d * ((d * ((d * 2696065) + (e * 3747750))) + (e * (e * 2935145)))) + (e * (e * (e * 1436070))))) + (e * (e * (e * (e * 294155))))))) + ((d * ((d * ((d * ((d * ((d * 2276212) + (e * 3872840))) + (e * (e * 4386550)))) + (e * (e * (e * 3457900))))) + (e * (e * (e * (e * 1465850)))))) + (e * (e * (e * (e * (e * 247966)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 1279875) + (e * 2591820))) + (e * (e * 4093055)))) + (e * (e * (e * 4602460))))) + (e * (e * (e * (e * 3014005)))))) + (e * (e * (e * (e * (e * 1049980))))))) + (e * (e * (e * (e * (e * (e * 153410))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 469370) + (e * 1124850))) + (e * (e * 2444650)))) + (e * (e * (e * 3648580))))) + (e * (e * (e * (e * 3283780)))))) + (e * (e * (e * (e * (e * 1783130))))))) + (e * (e * (e * (e * (e * (e * 548930)))))))) + (e * (e * (e * (e * (e * (e * (e * 73810)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 105645) + (e * 303340))) + (e * (e * 907315)))) + (e * (e * (e * 1723610))))) + (e * (e * (e * (e * 2023520)))))) + (e * (e * (e * (e * (e * 1543550))))))) + (e * (e * (e * (e * (e * (e * 753760)))))))) + (e * (e * (e * (e * (e * (e * (e * 213730))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 26565))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 12540) + (e * 44650))) + (e * (e * 189550)))) + (e * (e * (e * 454780))))) + (e * (e * (e * (e * 686670)))))) + (e * (e * (e * (e * (e * 698530))))))) + (e * (e * (e * (e * (e * (e * 477730)))))))) + (e * (e * (e * (e * (e * (e * (e * 210120))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 53610)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * (e * 2420)) + (e * (e * 16985)))) + (e * (e * (e * 53420))))) + (e * (e * (e * (e * 103900)))))) + (e * (e * (e * (e * (e * 134894))))))) + (e * (e * (e * (e * (e * (e * 118770)))))))) + (e * (e * (e * (e * (e * (e * (e * 70200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 26805)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010))))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * (e * 117))))))))))))

private theorem strong0_part_0_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_0_0 c d e := by
  unfold strong0_part_0_0
  positivity

theorem strong0_part_0_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 0) 0 = strong0_part_0_0 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong0_part_0_0 <;> ring

theorem strong0_part_0_0_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly0 c d e 0) 0 := by
  rw [strong0_part_0_0_eq]
  exact strong0_part_0_0_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
