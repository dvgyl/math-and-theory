module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber2

/-!
# Chamber 2 (ordering `01324`): coefficient of `a⁰ b^3`

Generated certificate. The coefficient of `b^3` in the constant term (in the smallest weight
`a`) of the chamber polynomial `chamberPoly2` is an explicit polynomial in `c`, `d`, `e` with
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

def strong2_part_0_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 7923830) + ((d * 33798440) + (e * 17905740)))) + ((d * ((d * 69420720) + (e * 73420120))) + (e * (e * 22885920))))) + ((d * ((d * ((d * 86306770) + (e * 137441030))) + (e * (e * 90178870)))) + (e * (e * (e * 21013850)))))) + ((d * ((d * ((d * ((d * 67834180) + (e * 145482880))) + (e * (e * 148127630)))) + (e * (e * (e * 71686300))))) + (e * (e * (e * (e * 13296080))))))) + ((d * ((d * ((d * ((d * ((d * 32769840) + (e * 89296590))) + (e * (e * 124504340)))) + (e * (e * (e * 92673330))))) + (e * (e * (e * (e * 35054070)))))) + (e * (e * (e * (e * (e * 5323990)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 8827340) + (e * 29554320))) + (e * (e * 52929400)))) + (e * (e * (e * 53730240))))) + (e * (e * (e * (e * 31033610)))))) + (e * (e * (e * (e * (e * 9537760))))))) + (e * (e * (e * (e * (e * (e * 1221730))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 1006480) + (e * 4065500))) + (e * (e * 9044080)))) + (e * (e * (e * 11788230))))) + (e * (e * (e * (e * 9269170)))))) + (e * (e * (e * (e * (e * 4340240))))))) + (e * (e * (e * (e * (e * (e * 1123320)))))))) + (e * (e * (e * (e * (e * (e * (e * 124540)))))))))

private theorem strong2_part_0_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong2_part_0_3 c d e := by
  unfold strong2_part_0_3
  positivity

theorem strong2_part_0_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly2 c d e 0) 3 = strong2_part_0_3 c d e := by
  dsimp only [chamberPoly2, residualOuter]
  simp only [ite_eq_left (show (0 : Fin 11) = 0 from rfl)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart0, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift2_0_eq, compactShift2_1_eq, compactShift2_2_eq,
    compactShift2_3_eq, compactShift2_4_eq, compactShift2_5_eq,
    compactGram2_0_eq, compactGram2_1_eq, compactGram2_2_eq]
  dsimp only [compactShift2_0, compactShift2_1, compactShift2_2,
    compactShift2_3, compactShift2_4, compactShift2_5,
    compactGram2_0, compactGram2_1, compactGram2_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly2, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong2_part_0_3 <;> ring

theorem strong2_part_0_3_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly2 c d e 0) 3 := by
  rw [strong2_part_0_3_eq]
  exact strong2_part_0_3_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
