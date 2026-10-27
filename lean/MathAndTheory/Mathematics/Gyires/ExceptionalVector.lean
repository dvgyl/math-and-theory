module

public import MathAndTheory.Mathematics.Gyires.ExceptionalTheorem

@[expose] public section

open MathAndTheory.Gyires.Bernoulli
open MathAndTheory.GyiresCirculant5.PermanentGram

namespace MathAndTheory.Gyires.Exceptional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HasExceptionalVector (A : Matrix ι ι ℝ) : Prop :=
  (∃ e, HasExceptionalColumn A e) ∨ (∃ e, HasExceptionalColumn A.transpose e)

omit [DecidableEq ι] in
lemma transpose_eq_uniform_iff (A : Matrix ι ι ℝ) :
    A.transpose = uniformMatrix ↔ A = uniformMatrix := by
  constructor
  · intro h
    have ht := congrArg Matrix.transpose h
    simpa only [Matrix.transpose_transpose, uniformMatrix_transpose] using ht
  · intro h
    rw [h, uniformMatrix_transpose]

theorem exceptional_vector_strong (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalVector A)
    (hn : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant (Fintype.card ι) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  rcases he with ⟨e, he⟩ | ⟨e, he⟩
  · exact exceptional_strong A e hA he hn
  · have h := exceptional_strong A.transpose e (transpose_mem_doublyStochastic_iff.mpr hA) he hn
    simp only [Matrix.transpose_transpose, Matrix.permanent_transpose] at h
    exact ⟨h.2, h.1⟩

theorem exceptional_vector_gram_eq_iff (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalVector A)
    (hn : 2 ≤ Fintype.card ι) :
    (dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent = A.permanent^2 ↔
      A = uniformMatrix) ∧
    (dimensionConstant (Fintype.card ι) * (A.transpose*A).permanent = A.permanent^2 ↔
      A = uniformMatrix) := by
  rcases he with ⟨e, he⟩ | ⟨e, he⟩
  · exact ⟨exceptional_left_strong_eq_iff A e hA he,
      (exceptional_right_bounds A e hA he hn).2⟩
  · have ht : A.transpose ∈ doublyStochastic ℝ ι := transpose_mem_doublyStochastic_iff.mpr hA
    have hl := exceptional_left_strong_eq_iff A.transpose e ht he
    have hr := (exceptional_right_bounds A.transpose e ht he hn).2
    simp only [Matrix.transpose_transpose, Matrix.permanent_transpose, transpose_eq_uniform_iff] at hl hr
    exact ⟨hr, hl⟩

theorem exceptional_vector_gyires (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalVector A)
    (hn : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card ι) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) ≤
        4*A.permanent^2 := by
  obtain ⟨hl, hr⟩ := exceptional_vector_strong A hA he hn
  have hs := permanent_square_bound_of_gram_bounds A (dimensionConstant (Fintype.card ι))
    (A.permanent^2) (dimensionConstant_nonneg _) hl hr
  linarith

theorem exceptional_vector_gyires_eq_iff (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalVector A)
    (hn : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card ι) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) =
        4*A.permanent^2 ↔ A = uniformMatrix := by
  constructor
  · intro hEq
    by_contra hne
    obtain ⟨hl, hr⟩ := exceptional_vector_strong A hA he hn
    have hlt : dimensionConstant (Fintype.card ι)*(A*A.transpose).permanent < A.permanent^2 :=
      lt_of_le_of_ne hl (fun h => hne ((exceptional_vector_gram_eq_iff A hA he hn).1.mp h))
    have hs := gyires_lt_of_strong A (dimensionConstant (Fintype.card ι))
      (dimensionConstant_nonneg _) hlt hr
    linarith
  · intro hu
    rw [hu, uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
    ring


end MathAndTheory.Gyires.Exceptional
