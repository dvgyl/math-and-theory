module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a⁰ b^2`

Generated certificate. The coefficient of `b^2` in the constant term (in the smallest weight
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

def strong1_part_0_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 2609120) + ((d * 15015010) + (e * 8507410)))) + ((d * ((d * 39720550) + (e * 45833770))) + (e * (e * 15249135))))) + ((d * ((d * ((d * 60623610) + (e * 106536870))) + (e * (e * 72986160)))) + (e * (e * (e * 17244180)))))) + ((d * ((d * ((d * ((d * 57300330) + (e * 135890310))) + (e * (e * 143418015)))) + (e * (e * (e * 69598550))))) + (e * (e * (e * (e * 12607820))))))) + ((d * ((d * ((d * ((d * ((d * 33978790) + (e * 101618740))) + (e * (e * 146976770)))) + (e * (e * (e * 110133630))))) + (e * (e * (e * (e * 41149510)))))) + (e * (e * (e * (e * (e * 6080250)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 12269965) + (e * 44169660))) + (e * (e * 82257090)))) + (e * (e * (e * 84959280))))) + (e * (e * (e * (e * 49310250)))))) + (e * (e * (e * (e * (e * 15094320))))))) + (e * (e * (e * (e * (e * (e * 1904260))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2459220) + (e * 10248230))) + (e * (e * 23645970)))) + (e * (e * (e * 31732680))))) + (e * (e * (e * (e * 25572100)))))) + (e * (e * (e * (e * (e * 12228120))))))) + (e * (e * (e * (e * (e * (e * 3218860)))))))) + (e * (e * (e * (e * (e * (e * (e * 361830)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 209000) + (e * 969180))) + (e * (e * 2699725)))) + (e * (e * (e * 4549220))))) + (e * (e * (e * (e * 4804120)))))) + (e * (e * (e * (e * (e * 3210610))))))) + (e * (e * (e * (e * (e * (e * 1329665)))))))) + (e * (e * (e * (e * (e * (e * (e * 313500))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 32335))))))))))

private theorem strong1_part_0_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_0_2 c d e := by
  unfold strong1_part_0_2
  positivity

theorem strong1_part_0_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 0) 2 = strong1_part_0_2 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong1_part_0_2 <;> ring

theorem strong1_part_0_2_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly1 c d e 0) 2 := by
  rw [strong1_part_0_2_eq]
  exact strong1_part_0_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
