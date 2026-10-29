module

public import GapFive
public import GapSix

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open Matrix Equiv

theorem actual_order_five_gram_bounds {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A : Matrix (Fin 5) (Fin 5) ℝ :=
      a • 1 + b • (finRotate 5).permMatrix ℝ + c • ((finRotate 5).permMatrix ℝ)^2
    (24/625 : ℝ) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      (24/625 : ℝ) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  have h := cycle_order_five_both_gram ha hb hc
  norm_num [dimensionConstant] at h
  exact h

theorem actual_order_six_gram_bounds {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A : Matrix (Fin 6) (Fin 6) ℝ :=
      a • 1 + b • (finRotate 6).permMatrix ℝ + c • ((finRotate 6).permMatrix ℝ)^2
    (5/324 : ℝ) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      (5/324 : ℝ) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  have h := cycle_order_six_both_gram ha hb hc
  norm_num [dimensionConstant] at h
  exact h

end MathAndTheory.Gyires.PermutationCoefficientStage

#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.u_six_zero
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.u_six_one
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.u_six_steps
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_uSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.v_six_zero
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.v_six_one
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.v_six_steps
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_vSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.w_six_zero
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.w_six_one
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.w_six_steps
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_wSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.ap_five_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.cp_five_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.fp_five_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.t1_five_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.t2_five_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_apFive
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_cpFive
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_fpFive
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_t1Five
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_t2Five
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.ap_six_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.cp_six_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.fp_six_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.t1_six_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.t2_six_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_apSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_cpSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_fpSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_t1Six
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_t2Six
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.gap_five_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.gap_five_coefficients
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_squareFive
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_gramFive
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_gapFive
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.chamber_five_nonneg
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.cycle_order_five_both_gram
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.gap_six_identity
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.gap_six_coefficients
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_squareSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_gramSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.eval_gapSix
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.chamber_six_nonneg
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.cycle_order_six_both_gram
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.actual_order_five_gram_bounds
#print axioms MathAndTheory.Gyires.PermutationCoefficientStage.actual_order_six_gram_bounds
