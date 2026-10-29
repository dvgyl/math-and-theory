module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a⁰ b^1`

Generated certificate. The coefficient of `b^1` in the constant term (in the smallest weight
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

def strong5_part_0_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 508000) + ((d * 3213670) + (e * 1269160)))) + ((d * ((d * 9442530) + (e * 7207860))) + (e * (e * 1798840))))) + ((d * ((d * ((d * 16316070) + (e * 18341100))) + (e * (e * 9604170)))) + (e * (e * (e * 2237490)))))) + ((d * ((d * ((d * ((d * 17956710) + (e * 26754400))) + (e * (e * 22313340)))) + (e * (e * (e * 11032060))))) + (e * (e * (e * (e * 2232210))))))) + ((d * ((d * ((d * ((d * ((d * 12916930) + (e * 24237000))) + (e * (e * 29023100)))) + (e * (e * (e * 22699210))))) + (e * (e * (e * (e * 9437990)))))) + (e * (e * (e * (e * (e * 1568350)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 6038020) + (e * 13933000))) + (e * (e * 22780000)))) + (e * (e * (e * 24968720))))) + (e * (e * (e * (e * 15979490)))))) + (e * (e * (e * (e * (e * 5449860))))))) + (e * (e * (e * (e * (e * (e * 772570))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1762340) + (e * 4978210))) + (e * (e * 10809180)))) + (e * (e * (e * 15533890))))) + (e * (e * (e * (e * 13653240)))))) + (e * (e * (e * (e * (e * 7216170))))))) + (e * (e * (e * (e * (e * (e * 2125230)))))))) + (e * (e * (e * (e * (e * (e * (e * 268070)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 290000) + (e * 1015760))) + (e * (e * 2885820)))) + (e * (e * (e * 5230680))))) + (e * (e * (e * (e * 5961230)))))) + (e * (e * (e * (e * (e * 4361820))))))) + (e * (e * (e * (e * (e * (e * 1999880)))))))) + (e * (e * (e * (e * (e * (e * (e * 522660))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59140))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 20240) + (e * 91080))) + (e * (e * 337460)))) + (e * (e * (e * 756070))))) + (e * (e * (e * (e * 1081450)))))) + (e * (e * (e * (e * (e * 1025970))))))) + (e * (e * (e * (e * (e * (e * 644570)))))))) + (e * (e * (e * (e * (e * (e * (e * 258200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong5_part_0_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong5_part_0_1 c d e := by
  unfold strong5_part_0_1
  positivity

theorem strong5_part_0_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly5 c d e 0) 1 = strong5_part_0_1 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong5_part_0_1 <;> ring

theorem strong5_part_0_1_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly5 c d e 0) 1 := by
  rw [strong5_part_0_1_eq]
  exact strong5_part_0_1_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
