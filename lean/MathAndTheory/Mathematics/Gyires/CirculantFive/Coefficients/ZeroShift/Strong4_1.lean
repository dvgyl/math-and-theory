module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a⁰ b^1`

Generated certificate. The coefficient of `b^1` in the constant term (in the smallest weight
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

def strong4_part_0_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 508000) + ((d * 3213670) + (e * 1944510)))) + ((d * ((d * 9442530) + (e * 11677200))) + (e * (e * 4033510))))) + ((d * ((d * ((d * 16316070) + (e * 30607110))) + (e * (e * 21870180)))) + (e * (e * (e * 5341650)))))) + ((d * ((d * ((d * ((d * 17956710) + (e * 45072440))) + (e * (e * 49790400)))) + (e * (e * (e * 25158260))))) + (e * (e * (e * (e * 4715800))))))) + ((d * ((d * ((d * ((d * ((d * 12916930) + (e * 40347650))) + (e * (e * 61244400)))) + (e * (e * (e * 48117390))))) + (e * (e * (e * (e * 18745520)))))) + (e * (e * (e * (e * (e * 2873460)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 6038020) + (e * 22295120))) + (e * (e * 43685300)))) + (e * (e * (e * 47581680))))) + (e * (e * (e * (e * 28993630)))))) + (e * (e * (e * (e * (e * 9286080))))))) + (e * (e * (e * (e * (e * (e * 1218500))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1762340) + (e * 7358170))) + (e * (e * 17949060)))) + (e * (e * (e * 25520760))))) + (e * (e * (e * (e * 21727180)))))) + (e * (e * (e * (e * (e * 10968000))))))) + (e * (e * (e * (e * (e * (e * 3030070)))))))) + (e * (e * (e * (e * (e * (e * (e * 353650)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 290000) + (e * 1304240))) + (e * (e * 3895500)))) + (e * (e * (e * 6993280))))) + (e * (e * (e * (e * 7843530)))))) + (e * (e * (e * (e * (e * 5581100))))))) + (e * (e * (e * (e * (e * (e * 2451340)))))))) + (e * (e * (e * (e * (e * (e * (e * 607760))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 20240) + (e * 91080))) + (e * (e * 337460)))) + (e * (e * (e * 756070))))) + (e * (e * (e * (e * 1081450)))))) + (e * (e * (e * (e * (e * 1025970))))))) + (e * (e * (e * (e * (e * (e * 644570)))))))) + (e * (e * (e * (e * (e * (e * (e * 258200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong4_part_0_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_0_1 c d e := by
  unfold strong4_part_0_1
  positivity

theorem strong4_part_0_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 0) 1 = strong4_part_0_1 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong4_part_0_1 <;> ring

theorem strong4_part_0_1_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly4 c d e 0) 1 := by
  rw [strong4_part_0_1_eq]
  exact strong4_part_0_1_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
