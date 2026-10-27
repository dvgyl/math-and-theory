module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_0
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_1
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_2
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_3
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_4
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_5
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_6
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_7
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_8
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_9
public import MathAndTheory.Mathematics.GyiresCirculant5.Coefficients.Strong3_10

/-!
# The margin in chamber 3 (ordering `01342`)

`strong_chamber_3`: if `a, b, c, d, e ≥ 0` and the weights are `a ≤ a + b ≤ ⋯ ≤ a + b + c + d
+ e` placed in the order `01342`, then `strongDefect ≥ 484 (b¹⁰ + c¹⁰ + d¹⁰ + e¹⁰)`.
Every coefficient of the chamber polynomial in `a` is nonnegative by the generated certificates
in `Coefficients/`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace MathAndTheory.GyiresCirculant5

theorem strong_chamber_3 (a b c d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) ≤ strongDefect (![a, a + b, a + b + c + d + e, a + b + c, a + b + c + d]) := by
  have hn : 0 ≤ eval11 (fun j => polyEval (chamberPoly3 c d e j) b) a := by
    apply eval11_nonneg _ a ha
    apply forall_fin11
    · exact strong3_coeff_0_nonneg b c d e hb hc hd he
    · exact strong3_coeff_1_nonneg b c d e hb hc hd he
    · exact strong3_coeff_2_nonneg b c d e hb hc hd he
    · exact strong3_coeff_3_nonneg b c d e hb hc hd he
    · exact strong3_coeff_4_nonneg b c d e hb hc hd he
    · exact strong3_coeff_5_nonneg b c d e hb hc hd he
    · exact strong3_coeff_6_nonneg b c d e hb hc hd he
    · exact strong3_coeff_7_nonneg b c d e hb hc hd he
    · exact strong3_coeff_8_nonneg b c d e hb hc hd he
    · exact strong3_coeff_9_nonneg b c d e hb hc hd he
    · exact strong3_coeff_10_nonneg b c d e hb hc hd he
  rw [chamberPoly3_eval] at hn
  exact sub_nonneg.mp hn

end MathAndTheory.GyiresCirculant5
