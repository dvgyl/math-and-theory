module

public import PermutationComplete

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCompleteAudit

open MathAndTheory.Gyires
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.PermutationComplete

theorem actual_permutation_polynomial_gram_bounds (n : ℕ) (p : Equiv.Perm (Fin n))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A : Matrix (Fin n) (Fin n) ℝ := a • 1 + b • p.permMatrix ℝ + c • (p.permMatrix ℝ)^2
    ((n.factorial : ℝ)/(n : ℝ)^n) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      ((n.factorial : ℝ)/(n : ℝ)^n) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  simpa only [polynomialMatrix, dimensionConstant, Fintype.card_fin] using
    permutation_polynomial_gram_bounds p ha hb hc

theorem actual_permutation_polynomial_square_bound (n : ℕ) (p : Equiv.Perm (Fin n))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A : Matrix (Fin n) (Fin n) ℝ := a • 1 + b • p.permMatrix ℝ + c • (p.permMatrix ℝ)^2
    ((n.factorial : ℝ)/(n : ℝ)^n) * (A^2).permanent ≤ A.permanent^2 := by
  simpa only [polynomialMatrix, dimensionConstant, Fintype.card_fin, pow_two] using
    permutation_polynomial_square_bound p ha hb hc

theorem actual_permutation_polynomial_gyires_bound (n : ℕ) (p : Equiv.Perm (Fin n))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A : Matrix (Fin n) (Fin n) ℝ := a • 1 + b • p.permMatrix ℝ + c • (p.permMatrix ℝ)^2
    ((n.factorial : ℝ)/(n : ℝ)^n) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A^2).permanent)
      ≤ 4*A.permanent^2 := by
  simpa only [polynomialMatrix, dimensionConstant, Fintype.card_fin, pow_two] using
    permutation_polynomial_gyires_bound p ha hb hc

theorem actual_cycle_strict_gyires_bound (n : ℕ) (hn : 23 ≤ n)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) :
    let Q := (finRotate n).permMatrix ℝ
    let A : Matrix (Fin n) (Fin n) ℝ := a • 1 + b • Q + c • Q^2
    ((n.factorial : ℝ)/(n : ℝ)^n) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A^2).permanent)
      < 4*A.permanent^2 := by
  simpa only [polynomialMatrix, dimensionConstant, pow_two] using
    cycle_strict_gyires_bound n hn ha hb hc hpositive

end MathAndTheory.Gyires.PermutationCompleteAudit

#print axioms MathAndTheory.Gyires.PermutationComplete.cycle_all_gram_bounds
#print axioms MathAndTheory.Gyires.PermutationComplete.permutation_polynomial_gram_bounds
#print axioms MathAndTheory.Gyires.PermutationComplete.permutation_polynomial_square_bound
#print axioms MathAndTheory.Gyires.PermutationComplete.permutation_polynomial_gyires_bound
#print axioms MathAndTheory.Gyires.PermutationComplete.cycle_strict_square_bound
#print axioms MathAndTheory.Gyires.PermutationComplete.cycle_strict_gyires_bound
#print axioms MathAndTheory.Gyires.PermutationCompleteAudit.actual_permutation_polynomial_gram_bounds
#print axioms MathAndTheory.Gyires.PermutationCompleteAudit.actual_permutation_polynomial_square_bound
#print axioms MathAndTheory.Gyires.PermutationCompleteAudit.actual_permutation_polynomial_gyires_bound
#print axioms MathAndTheory.Gyires.PermutationCompleteAudit.actual_cycle_strict_gyires_bound
