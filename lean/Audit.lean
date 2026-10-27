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

example {n : Type*} [Fintype n] [DecidableEq n] (M N : Matrix n n ℝ) :
    |(M * N.transpose).permanent| ≤
      Real.sqrt ((M * M.transpose).permanent * (N * N.transpose).permanent) :=
  MathAndTheory.GyiresCirculant5.PermanentGram.permanent_mul_transpose_abs_le M N

example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (σ τ : Equiv.Perm n) :
    (A.submatrix σ τ).permanent = A.permanent :=
  MathAndTheory.Gyires.permanent_submatrix_perm A σ τ

example (dims : List ℕ) (hpos : ∀ n ∈ dims, 0 < n) :
    (dims.sum.factorial : ℝ) / (dims.sum : ℝ) ^ dims.sum ≤
      (dims.map (fun (n : ℕ) => (n.factorial : ℝ) / (n : ℝ) ^ n)).prod :=
  MathAndTheory.Gyires.dimensionConstant_sum_le dims hpos


namespace MathAndTheory.Gyires
open scoped BigOperators

example {r : ℕ} (m : Fin r → ℕ)
    (B : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (σ τ : Equiv.Perm (Sigma (fun i => Fin (m i))))
    (hm : ∀ i, 0 < m i)
    (hB : ∀ i, B i ∈ doublyStochastic ℝ (Fin (m i)))
    (hs : ∀ i,
      dimensionConstant (m i) * (B i * (B i).transpose).permanent ≤ (B i).permanent ^ 2 ∧
      dimensionConstant (m i) * ((B i).transpose * B i).permanent ≤ (B i).permanent ^ 2) :
    let A := (Matrix.blockDiagonal' B).submatrix σ τ
    A ∈ doublyStochastic ℝ (Sigma (fun i => Fin (m i))) ∧
      dimensionConstant (∑ i, m i) * (A * A.transpose).permanent ≤ A.permanent ^ 2 ∧
      dimensionConstant (∑ i, m i) * (A.transpose * A).permanent ≤ A.permanent ^ 2 ∧
      dimensionConstant (∑ i, m i) * ((A * A.transpose).permanent +
        (A.transpose * A).permanent + 2 * (A * A).permanent) ≤ 4 * A.permanent ^ 2 := by
  have h := strong_bounds_blockDiagonal_submatrix_perm B σ τ
    (by simpa only [Fintype.card_fin] using hm)
    (by simpa only [Fintype.card_fin] using hs)
  have hg := gyires_blockDiagonal_submatrix_perm B σ τ
    (by simpa only [Fintype.card_fin] using hm)
    (by simpa only [Fintype.card_fin] using hs)
  refine ⟨blockDiagonal_submatrix_mem_doublyStochastic B σ τ hB, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using h.1
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using h.2
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using hg

example {r : ℕ} (m : Fin r → ℕ)
    (B : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (σ τ : Equiv.Perm (Sigma (fun i => Fin (m i))))
    (hm : ∀ i, 0 < m i) (hr : 2 ≤ r)
    (hB : ∀ i, B i ∈ doublyStochastic ℝ (Fin (m i)))
    (hs : ∀ i,
      dimensionConstant (m i) * (B i * (B i).transpose).permanent ≤ (B i).permanent ^ 2 ∧
      dimensionConstant (m i) * ((B i).transpose * B i).permanent ≤ (B i).permanent ^ 2) :
    let A := (Matrix.blockDiagonal' B).submatrix σ τ
    dimensionConstant (∑ i, m i) * (A * A.transpose).permanent < A.permanent ^ 2 ∧
      dimensionConstant (∑ i, m i) * (A.transpose * A).permanent < A.permanent ^ 2 ∧
      dimensionConstant (∑ i, m i) * ((A * A.transpose).permanent +
        (A.transpose * A).permanent + 2 * (A * A).permanent) < 4 * A.permanent ^ 2 := by
  have h := strong_bounds_blockDiagonal_submatrix_perm_lt B σ τ
    (by simpa only [Fintype.card_fin] using hm)
    (by simpa only [Fintype.card_fin] using hr) hB
    (by simpa only [Fintype.card_fin] using hs)
  have hg := gyires_blockDiagonal_submatrix_perm_lt B σ τ
    (by simpa only [Fintype.card_fin] using hm)
    (by simpa only [Fintype.card_fin] using hr) hB
    (by simpa only [Fintype.card_fin] using hs)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using h.1
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using h.2
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using hg

end MathAndTheory.Gyires

open MathAndTheory.Gyires MathAndTheory.Gyires.CirculantCertificate
example (hP : ∀ σ : Equiv.Perm (Fin 6),
    ∀ d ∈ (strongPolynomial σ).support, 0 ≤ (strongPolynomial σ).coeff d)
    (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * (circulant w * (circulant w).transpose).permanent ≤
      324 * (circulant w).permanent ^ 2 := by
  have h := strong_circulant_of_coeff_nonneg hP w hw
  norm_num [dimensionConstant] at h
  linarith

example (hP : ∀ σ : Equiv.Perm (Fin 7),
    ∀ d ∈ (strongPolynomial σ).support, 0 ≤ (strongPolynomial σ).coeff d)
    (w : Fin 7 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    720 * (circulant w * (circulant w).transpose).permanent ≤
      117649 * (circulant w).permanent ^ 2 := by
  have h := strong_circulant_of_coeff_nonneg hP w hw
  norm_num [dimensionConstant] at h
  linarith

example (hP : ∀ σ : Equiv.Perm (Fin 7),
    ∀ d ∈ (strongPolynomial σ).support, 0 ≤ (strongPolynomial σ).coeff d)
    (w : Fin 7 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    720 * ((circulant w * (circulant w).transpose).permanent +
      ((circulant w).transpose * circulant w).permanent +
      2 * (circulant w * circulant w).permanent) ≤
        470596 * (circulant w).permanent ^ 2 := by
  have h := gyires_circulant_of_coeff_nonneg hP w hw
  norm_num [dimensionConstant] at h
  linarith

audit_math_and_theory
