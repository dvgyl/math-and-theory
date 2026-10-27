module

public import MathAndTheory.Mathematics.Gyires.FourBlock

@[expose] public section

open scoped BigOperators
open MathAndTheory.Gyires MathAndTheory.Gyires.Bernoulli

namespace MathAndTheory.Gyires.Exceptional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HasExceptionalColumn (A : Matrix ι ι ℝ) (e : ι) : Prop :=
  ∀ i j k, j ≠ e → k ≠ e → A i j = A i k

omit [Fintype ι] in
lemma exceptional_has_column_classes (A : Matrix ι ι ℝ) (e : ι)
    (he : HasExceptionalColumn A e) : HasColumnClasses A (fun j => decide (j = e)) := by
  intro i j k h
  by_cases hj : j = e
  · have hk : k = e := by simpa [hj] using h.symm
    subst j
    subst k
    rfl
  · have hk : k ≠ e := by simpa [hj] using h
    exact he i j k hj hk

theorem exceptional_left_bounds (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e) :
    (A * A.transpose).permanent ≤ A.permanent ∧
      dimensionConstant (Fintype.card ι) ≤ A.permanent ∧
      (A.permanent = dimensionConstant (Fintype.card ι) ↔ A = uniformMatrix) :=
  column_class_bounds A (fun j => decide (j = e)) hA (exceptional_has_column_classes A e he)

theorem exceptional_left_strong (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e) :
    dimensionConstant (Fintype.card ι) * (A * A.transpose).permanent ≤ A.permanent^2 := by
  obtain ⟨hg, hd, _⟩ := exceptional_left_bounds A e hA he
  have hc := dimensionConstant_nonneg (Fintype.card ι)
  have hp : 0 ≤ A.permanent := hc.trans hd
  have h1 := mul_le_mul_of_nonneg_left hg hc
  have h2 := mul_le_mul_of_nonneg_right hd hp
  nlinarith

theorem exceptional_left_strong_eq_iff (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e) :
    dimensionConstant (Fintype.card ι) * (A * A.transpose).permanent = A.permanent^2 ↔
      A = uniformMatrix := by
  constructor
  · intro hEq
    obtain ⟨hg, hd, heq⟩ := exceptional_left_bounds A e hA he
    apply heq.mp
    have hc := dimensionConstant_pos_all (Fintype.card ι)
    have hp : 0 < A.permanent := hc.trans_le hd
    have h1 := mul_le_mul_of_nonneg_left hg hc.le
    nlinarith
  · intro hu
    rw [hu, uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
    ring


end MathAndTheory.Gyires.Exceptional
