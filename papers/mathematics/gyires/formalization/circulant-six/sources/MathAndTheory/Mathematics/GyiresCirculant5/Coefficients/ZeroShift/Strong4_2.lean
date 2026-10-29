module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a⁰ b^2`

Generated certificate. The coefficient of `b^2` in the constant term (in the smallest weight
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

def strong4_part_0_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 2609120) + ((d * 14365360) + (e * 8507410)))) + ((d * ((d * 36638075) + (e * 44216370))) + (e * (e * 15249135))))) + ((d * ((d * ((d * 54437890) + (e * 98939700))) + (e * (e * 70241190)))) + (e * (e * (e * 17244180)))))) + ((d * ((d * ((d * ((d * 50604830) + (e * 121793650))) + (e * (e * 132738210)))) + (e * (e * (e * 67053630))))) + (e * (e * (e * (e * 12607820))))))) + ((d * ((d * ((d * ((d * ((d * 29852590) + (e * 88214950))) + (e * (e * 130853200)))) + (e * (e * (e * 102110810))))) + (e * (e * (e * (e * 39683020)))))) + (e * (e * (e * (e * (e * 6080250)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 10872070) + (e * 37351650))) + (e * (e * 70666665)))) + (e * (e * (e * 75876170))))) + (e * (e * (e * (e * 45804690)))))) + (e * (e * (e * (e * (e * 14571990))))))) + (e * (e * (e * (e * (e * (e * 1904260))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2234840) + (e * 8507080))) + (e * (e * 19731630)))) + (e * (e * (e * 27425860))))) + (e * (e * (e * (e * 22941250)))))) + (e * (e * (e * (e * (e * 11416620))))))) + (e * (e * (e * (e * (e * (e * 3122470)))))))) + (e * (e * (e * (e * (e * (e * (e * 361830)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 198920) + (e * 795680))) + (e * (e * 2209550)))) + (e * (e * (e * 3843770))))) + (e * (e * (e * (e * 4198755)))))) + (e * (e * (e * (e * (e * 2919520))))))) + (e * (e * (e * (e * (e * (e * 1258755)))))))) + (e * (e * (e * (e * (e * (e * (e * 307010))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 32335))))))))))

private theorem strong4_part_0_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_0_2 c d e := by
  unfold strong4_part_0_2
  positivity

theorem strong4_part_0_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 0) 2 = strong4_part_0_2 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong4_part_0_2 <;> ring

theorem strong4_part_0_2_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly4 c d e 0) 2 := by
  rw [strong4_part_0_2_eq]
  exact strong4_part_0_2_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
