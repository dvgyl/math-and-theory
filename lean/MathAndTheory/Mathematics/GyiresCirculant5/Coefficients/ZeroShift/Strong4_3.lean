module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber4

/-!
# Chamber 4 (ordering `01423`): coefficient of `a⁰ b^3`

Generated certificate. The coefficient of `b^3` in the constant term (in the smallest weight
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

def strong4_part_0_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 7923830) + ((d * 37561070) + (e * 21668370)))) + ((d * ((d * 81851910) + (e * 95995900))) + (e * (e * 33030510))))) + ((d * ((d * ((d * 102163700) + (e * 179204680))) + (e * (e * 126226020)))) + (e * (e * (e * 31154280)))))) + ((d * ((d * ((d * ((d * 77319130) + (e * 177858020))) + (e * (e * 190870330)))) + (e * (e * (e * 96422280))))) + (e * (e * (e * (e * 18179550))))))) + ((d * ((d * ((d * ((d * ((d * 35154680) + (e * 98113600))) + (e * (e * 141862440)))) + (e * (e * (e * 110005690))))) + (e * (e * (e * (e * 42659620)))))) + (e * (e * (e * (e * (e * 6523110)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 8868560) + (e * 28392360))) + (e * (e * 51679130)))) + (e * (e * (e * 54748740))))) + (e * (e * (e * (e * 32798320)))))) + (e * (e * (e * (e * (e * 10358040))))))) + (e * (e * (e * (e * (e * (e * 1342890))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 959440) + (e * 3358040))) + (e * (e * 7365040)))) + (e * (e * (e * 10017500))))) + (e * (e * (e * (e * 8259380)))))) + (e * (e * (e * (e * (e * 4050590))))))) + (e * (e * (e * (e * (e * (e * 1091350)))))))) + (e * (e * (e * (e * (e * (e * (e * 124540)))))))))

private theorem strong4_part_0_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong4_part_0_3 c d e := by
  unfold strong4_part_0_3
  positivity

theorem strong4_part_0_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly4 c d e 0) 3 = strong4_part_0_3 c d e := by
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
  norm_num [polyCoeff] <;> unfold strong4_part_0_3 <;> ring

theorem strong4_part_0_3_coeff_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyCoeff (chamberPoly4 c d e 0) 3 := by
  rw [strong4_part_0_3_eq]
  exact strong4_part_0_3_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
