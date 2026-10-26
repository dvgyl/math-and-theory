module
import MathAndTheory
import Solutions.QPermanent
import Solutions.DomiRank
import Solutions.DiagonalConcavity
import Solutions.Hofstadter
import Solutions.Motzkin
import Solutions.BestOfN
import Solutions.GyiresCirculant5

/-!
Publication acceptance checks.  These type ascriptions restate the target claims,
so merely exporting a theorem with the expected name is insufficient.
The command at the end audits every loaded MathAndTheory theorem transitively.
-/

open MathAndTheory.QPermanent

example : counterexampleReal.PosDef := counterexample_posDef

example : qPermanent counterexampleReal (14 : ℝ) = 8968822249 := counterexample_q14

example : qPermanent counterexampleReal (15 : ℝ) = 7441960000 := counterexample_q15

example (q : ℝ) : qPermanent counterexampleReal q =
    625 + 25*q^3 + 800*q^5 + 25*q^7 + q^8*(q-16)^2 := by
  rw [counterexample_polynomial]
  ring

example : deriv (qPermanent counterexampleReal) 15 = -1563030000 :=
  counterexample_deriv_fifteen

example :
    ¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef → (∃ i j, i ≠ j ∧ A i j ≠ 0) →
      ∃ ε : ℝ, ε ≤ -1 ∧ StrictMonoOn (qPermanent A) (Set.Ioi ε)) :=
  not_daFonseca_extended_conjecture

example (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef ∧ deriv (qPermanent A) r < 0 :=
  exists_posDef_negative_qPermanent_derivative r hr

example (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      5 ≤ n ∧ A.PosDef ∧ deriv (qPermanent A) r < 0 :=
  exists_posDef_negative_qPermanent_derivative_ge_five r hr

example :
    ∃ A : Matrix (Fin 5) (Fin 5) ℝ,
      A.PosDef ∧ (∀ i, A i i = 1) ∧ qPermanent A 15 < qPermanent A 14 :=
  exists_correlation_counterexample

example (δ : ℝ) (hδ : 0 < δ) :
    ¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef → MonotoneOn (qPermanent A) (Set.Icc 1 (1+δ))) :=
  not_uniform_monotonicity_above_one δ hδ

example (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef ∧ (∀ i, A i i = 1) ∧ deriv (qPermanent A) r < 0 :=
  exists_correlation_negative_qPermanent_derivative r hr

example (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef ∧ (∀ i, A i i = 1) ∧ (∀ i j, A i j ≠ 0) ∧
        deriv (qPermanent A) r < 0 :=
  exists_dense_correlation_negative_qPermanent_derivative r hr

example (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ),
      Matrix.PosDef (fun i j => (B i j : ℝ)) ∧
        deriv (qPermanent (fun i j => (B i j : ℝ))) r < 0 :=
  exists_integer_posDef_negative_qPermanent_derivative r hr

#print axioms MathAndTheory.QPermanent.not_daFonseca_extended_conjecture
#print axioms MathAndTheory.QPermanent.exists_posDef_negative_qPermanent_derivative
#print axioms MathAndTheory.QPermanent.exists_dense_correlation_negative_qPermanent_derivative
#print axioms MathAndTheory.QPermanent.exists_integer_posDef_negative_qPermanent_derivative
#print axioms MathAndTheory.DomiRank.fourteen_vertex_counterexample
#print axioms MathAndTheory.DomiRank.spectral_bound_on_interval
#print axioms MathAndTheory.DomiRank.entropyNats_gap

-- Print the axiom list for each selected publication statement.
#print axioms MathAndTheory.Motzkin.Palomar.source_defined_result
#print axioms BestOfNChallenge.result
#print axioms BestOfNChallenge.every_budget_small_atoms
#print axioms ConcavityChallenge.result
#print axioms DomiRankProblem.counterexample
#print axioms MathAndTheory.GyiresCirculant5.gyires_ratio
#print axioms MathAndTheory.GyiresCirculant5.gyires_ratio_eq_iff
#print axioms MathAndTheory.GyiresCirculant5.gyires_denominator_pos
#print axioms MathAndTheory.GyiresCirculant5.gyires_homogeneous
#print axioms MathAndTheory.GyiresCirculant5.gyires_homogeneous_eq_iff
#print axioms MathAndTheory.GyiresCirculant5.strong_inequality
#print axioms MathAndTheory.GyiresCirculant5.strong_inequality_eq_iff
#print axioms MathAndTheory.GyiresCirculant5.strong_margin
#print axioms MathAndTheory.GyiresCirculant5.strong_margin_attained
#print axioms MathAndTheory.GyiresCirculant5.strong_margin_sharp
#print axioms HofstadterChallenge.result
#print axioms QPermanentProblem.finite_counterexample
#print axioms QPermanentProblem.extended_conjecture_false
#print axioms QPermanentProblem.negative_derivative_at_every_parameter
#print axioms QPermanentProblem.dense_correlation_counterexamples
#print axioms QPermanentProblem.integer_counterexamples

audit_math_and_theory
