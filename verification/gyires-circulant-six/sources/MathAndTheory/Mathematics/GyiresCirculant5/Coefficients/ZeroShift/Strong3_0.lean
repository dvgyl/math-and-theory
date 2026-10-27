module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber3

/-!
# Chamber 3 (ordering `01342`): coefficient of `a⁰ b^0`

Generated certificate. The coefficient of `b^0` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly3` is an explicit polynomial in `c`, `d`, `e` with
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

def strong3_part_0_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 43725) + ((d * 245840) + (e * 122920)))) + ((d * ((d * 689190) + (e * 689190))) + (e * (e * 186550))))) + ((d * ((d * ((d * 1256320) + (e * 1884480))) + (e * (e * 1136760)))) + (e * (e * (e * 254300)))))) + ((d * ((d * ((d * ((d * 1605135) + (e * 3210270))) + (e * (e * 3125785)))) + (e * (e * (e * 1520650))))) + (e * (e * (e * (e * 294155))))))) + ((d * ((d * ((d * ((d * ((d * 1457652) + (e * 3644130))) + (e * (e * 5001260)))) + (e * (e * (e * 3857760))))) + (e * (e * (e * (e * 1538910)))))) + (e * (e * (e * (e * (e * 247966)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 927170) + (e * 2781510))) + (e * (e * 5018680)))) + (e * (e * (e * 5401510))))) + (e * (e * (e * (e * 3347480)))))) + (e * (e * (e * (e * (e * 1110310))))))) + (e * (e * (e * (e * (e * (e * 153410))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 396460) + (e * 1387610))) + (e * (e * 3183790)))) + (e * (e * (e * 4490450))))) + (e * (e * (e * (e * 3865190)))))) + (e * (e * (e * (e * (e * 2001140))))))) + (e * (e * (e * (e * (e * (e * 581380)))))))) + (e * (e * (e * (e * (e * (e * (e * 73810)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 104665) + (e * 418660))) + (e * (e * 1217670)))) + (e * (e * (e * 2187700))))) + (e * (e * (e * (e * 2478635)))))) + (e * (e * (e * (e * (e * 1799540))))))) + (e * (e * (e * (e * (e * (e * 825150)))))))) + (e * (e * (e * (e * (e * (e * (e * 220220))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 26565))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 13980) + (e * 62910))) + (e * (e * 244100)))) + (e * (e * (e * 560770))))) + (e * (e * (e * (e * 820790)))))) + (e * (e * (e * (e * (e * 796840))))))) + (e * (e * (e * (e * (e * (e * 516670)))))))) + (e * (e * (e * (e * (e * (e * (e * 216610))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 53610)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * (e * 2420)) + (e * (e * 16985)))) + (e * (e * (e * 53420))))) + (e * (e * (e * (e * 103900)))))) + (e * (e * (e * (e * (e * 134894))))))) + (e * (e * (e * (e * (e * (e * 118770)))))))) + (e * (e * (e * (e * (e * (e * (e * 70200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 26805)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010))))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * (e * 117))))))))))))

private theorem strong3_part_0_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong3_part_0_0 c d e := by
  unfold strong3_part_0_0
  positivity

theorem strong3_part_0_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly3 c d e 0) 0 = strong3_part_0_0 c d e := by
  dsimp only [chamberPoly3, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift3_0_eq, compactShift3_1_eq, compactShift3_2_eq,
    compactShift3_3_eq, compactShift3_4_eq, compactShift3_5_eq,
    compactGram3_0_eq, compactGram3_1_eq, compactGram3_2_eq]
  dsimp only [compactShift3_0, compactShift3_1, compactShift3_2,
    compactShift3_3, compactShift3_4, compactShift3_5,
    compactGram3_0, compactGram3_1, compactGram3_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly3, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong3_part_0_0 <;> ring

theorem strong3_part_0_0_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly3 c d e 0) 0 := by
  rw [strong3_part_0_0_eq]
  exact strong3_part_0_0_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
