module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_0
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_1
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_2
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_3
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_4
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_5
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_6
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_7
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_8
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_9
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.ZeroShift.Strong5_10
public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber5

/-!
# Chamber 5 (ordering `01432`): coefficient of `a^0`

Generated certificate. The coefficient of `a^0` (a power of the smallest weight) in the chamber
polynomial `chamberPoly5` is a polynomial in the first gap `b` whose coefficients are explicit
polynomials in `c`, `d`, `e` with nonnegative integer coefficients. Each is proved equal to the
computed coefficient by `ring` and nonnegative by `positivity`, so the whole coefficient is
nonnegative for `b, c, d, e ≥ 0`.
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

theorem strong5_coeff_0_length (c d e : ℝ) :
    (chamberPoly5 c d e 0).length ≤ 11 := by
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
  norm_num

theorem strong5_coeff_0_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly5 c d e 0) b := by
  apply polyEval_nonneg_of_coeff _ b 11
    (strong5_coeff_0_length c d e) hb
  apply forall_fin11
  · exact strong5_part_0_0_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_1_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_2_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_3_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_4_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_5_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_6_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_7_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_8_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_9_coeff_nonneg c d e hc hd he
  · exact strong5_part_0_10_coeff_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
