module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a⁰ b^1`

Generated certificate. The coefficient of `b^1` in the constant term (in the smallest weight
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

def strong1_part_0_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 508000) + ((d * 3302840) + (e * 1944510)))) + ((d * ((d * 9933560) + (e * 11945900))) + (e * (e * 4033510))))) + ((d * ((d * ((d * 17489910) + (e * 32066720))) + (e * (e * 22389340)))) + (e * (e * (e * 5341650)))))) + ((d * ((d * ((d * ((d * 19517950) + (e * 48325760))) + (e * (e * 52242750)))) + (e * (e * (e * 25754840))))) + (e * (e * (e * (e * 4715800))))))) + ((d * ((d * ((d * ((d * ((d * 14156550) + (e * 44215040))) + (e * (e * 65915750)))) + (e * (e * (e * 50519360))))) + (e * (e * (e * (e * 19200780)))))) + (e * (e * (e * (e * (e * 2873460)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 6629910) + (e * 24908580))) + (e * (e * 48168190)))) + (e * (e * (e * 51264080))))) + (e * (e * (e * (e * 30485850)))))) + (e * (e * (e * (e * (e * 9518760))))))) + (e * (e * (e * (e * (e * (e * 1218500))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1926450) + (e * 8358660))) + (e * (e * 20206920)))) + (e * (e * (e * 28168120))))) + (e * (e * (e * (e * 23450390)))))) + (e * (e * (e * (e * (e * 11529750))))))) + (e * (e * (e * (e * (e * (e * 3100980)))))))) + (e * (e * (e * (e * (e * (e * (e * 353650)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 314020) + (e * 1508500))) + (e * (e * 4457170)))) + (e * (e * (e * 7870580))))) + (e * (e * (e * (e * 8664380)))))) + (e * (e * (e * (e * (e * 6009440))))))) + (e * (e * (e * (e * (e * (e * 2567680)))))))) + (e * (e * (e * (e * (e * (e * (e * 620740))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 21680) + (e * 109340))) + (e * (e * 392010)))) + (e * (e * (e * 862060))))) + (e * (e * (e * (e * 1215570)))))) + (e * (e * (e * (e * (e * 1124280))))))) + (e * (e * (e * (e * (e * (e * 683510)))))))) + (e * (e * (e * (e * (e * (e * (e * 264690))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong1_part_0_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_0_1 c d e := by
  unfold strong1_part_0_1
  positivity

theorem strong1_part_0_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 0) 1 = strong1_part_0_1 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong1_part_0_1 <;> ring

theorem strong1_part_0_1_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly1 c d e 0) 1 := by
  rw [strong1_part_0_1_eq]
  exact strong1_part_0_1_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
