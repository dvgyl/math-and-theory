module

public import MathAndTheory.Mathematics.Gyires.ExceptionalVector

@[expose] public section

open MathAndTheory.Gyires MathAndTheory.Gyires.Bernoulli

namespace MathAndTheory.GyiresExceptional

def HasExceptionalVector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∃ e, ∀ i j k, j ≠ e → k ≠ e → A i j = A i k) ∨
    (∃ e, ∀ i j k, j ≠ e → k ≠ e → A j i = A k i)

theorem strong {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    ((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      ((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  change MathAndTheory.Gyires.Exceptional.HasExceptionalVector A at he
  have h := MathAndTheory.Gyires.Exceptional.exceptional_vector_strong A hA he (by simpa using hn)
  simpa only [dimensionConstant, Fintype.card_fin, uniformMatrix, one_div] using h

theorem gram_eq_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    (((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A*A.transpose).permanent = A.permanent^2 ↔
      A = fun _ _ => 1 / (n : ℝ)) ∧
    (((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A.transpose*A).permanent = A.permanent^2 ↔
      A = fun _ _ => 1 / (n : ℝ)) := by
  change MathAndTheory.Gyires.Exceptional.HasExceptionalVector A at he
  have h := MathAndTheory.Gyires.Exceptional.exceptional_vector_gram_eq_iff A hA he (by simpa using hn)
  have hu : (MathAndTheory.Gyires.Bernoulli.uniformMatrix : Matrix (Fin n) (Fin n) ℝ) =
      (fun _ _ => 1 / (n : ℝ)) := by
    ext i j
    simp [MathAndTheory.Gyires.Bernoulli.uniformMatrix]
  simpa only [dimensionConstant, Fintype.card_fin, hu] using h

theorem gyires {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    ((Nat.factorial n : ℝ) / (n : ℝ)^n) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) ≤
        4*A.permanent^2 := by
  change MathAndTheory.Gyires.Exceptional.HasExceptionalVector A at he
  have h := MathAndTheory.Gyires.Exceptional.exceptional_vector_gyires A hA he (by simpa using hn)
  simpa only [dimensionConstant, Fintype.card_fin, uniformMatrix, one_div] using h

theorem gyires_eq_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    ((Nat.factorial n : ℝ) / (n : ℝ)^n) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) =
        4*A.permanent^2 ↔ A = fun _ _ => 1 / (n : ℝ) := by
  change MathAndTheory.Gyires.Exceptional.HasExceptionalVector A at he
  have h := MathAndTheory.Gyires.Exceptional.exceptional_vector_gyires_eq_iff A hA he (by simpa using hn)
  have hu : (MathAndTheory.Gyires.Bernoulli.uniformMatrix : Matrix (Fin n) (Fin n) ℝ) =
      (fun _ _ => 1 / (n : ℝ)) := by
    ext i j
    simp [MathAndTheory.Gyires.Bernoulli.uniformMatrix]
  simpa only [dimensionConstant, Fintype.card_fin, hu] using h

end MathAndTheory.GyiresExceptional
