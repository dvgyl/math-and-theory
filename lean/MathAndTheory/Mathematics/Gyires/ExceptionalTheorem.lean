module

public import MathAndTheory.Mathematics.Gyires.ExceptionalMatrix

@[expose] public section

open scoped BigOperators
open MathAndTheory.Gyires.Bernoulli
open MathAndTheory.GyiresCirculant5.PermanentGram

namespace MathAndTheory.Gyires.Exceptional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exceptional_right_bounds (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (hn : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card ι) * (A.transpose * A).permanent ≤ A.permanent^2 ∧
      (dimensionConstant (Fintype.card ι) * (A.transpose * A).permanent = A.permanent^2 ↔
        A = uniformMatrix) := by
  let k := Fintype.card ι - 2
  have hcard : Fintype.card ι = k+2 := by dsimp [k]; omega
  let u : ι → ℝ := fun i => A i e
  let B : ℝ := (((k : ℝ)+1)/((k : ℝ)+2))^(k+1)
  let C : ℝ := dimensionConstant (Fintype.card ι)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := dimensionConstant_pos_all _
  have hf : 0 < (C/B)^2 := by positivity
  have hp := exceptional_parameters A e hA
  have hprob := scalar_probability_bounds u hp.1 hp.2 k hcard
  have hper : A.permanent = C * (oneSuccess u / B) := exceptional_permanent A e hA he k hcard
  have hgram := exceptional_gram_permanent A e hA he k hcard
  have hr := special_reference_eq_scalarR (secondMoment u) e k hcard
  have hleft : C*(A.transpose*A).permanent = (C/B)^2*scalarR k (secondMoment u) := by
    rw [hgram, ← hr]
    dsimp only [C, B, u]
    field_simp
  have hright : A.permanent^2 = (C/B)^2*(oneSuccess u)^2 := by
    rw [hper]
    ring
  constructor
  · change C*(A.transpose*A).permanent ≤ A.permanent^2
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left hprob.1 hf.le
  · constructor
    · intro hEq
      change C*(A.transpose*A).permanent = A.permanent^2 at hEq
      rw [hleft, hright] at hEq
      have hscalar := mul_left_cancel₀ hf.ne' hEq
      have hu := scalar_probability_eq_implies_constant u hp.1 hp.2 k hcard hscalar
      have hshape := eq_exceptionalMatrix A e hA he (by omega : 1 < Fintype.card ι)
      rw [hshape]
      ext i j
      change (if j=e then u i else (1-u i)/(Fintype.card ι-1 : ℕ)) = 1/(Fintype.card ι : ℝ)
      rw [hu i, hcard]
      simp only [show k+2-1 = k+1 by omega, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      split_ifs
      · rfl
      · field_simp
        ring
    · intro hu
      rw [hu, uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
      ring

theorem exceptional_strong (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (hn : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant (Fintype.card ι) * (A.transpose*A).permanent ≤ A.permanent^2 :=
  ⟨exceptional_left_strong A e hA he, (exceptional_right_bounds A e hA he hn).1⟩

theorem exceptional_gyires (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (hn : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card ι) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) ≤
        4*A.permanent^2 := by
  obtain ⟨hl, hr⟩ := exceptional_strong A e hA he hn
  have hs := permanent_square_bound_of_gram_bounds A (dimensionConstant (Fintype.card ι))
    (A.permanent^2) (dimensionConstant_nonneg _) hl hr
  linarith

theorem exceptional_gyires_eq_iff (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (hn : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card ι) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) =
        4*A.permanent^2 ↔ A = uniformMatrix := by
  constructor
  · intro hEq
    by_contra hne
    obtain ⟨hl, hr⟩ := exceptional_strong A e hA he hn
    have hlt : dimensionConstant (Fintype.card ι)*(A*A.transpose).permanent < A.permanent^2 :=
      lt_of_le_of_ne hl (fun h => hne ((exceptional_left_strong_eq_iff A e hA he).mp h))
    have hs := gyires_lt_of_strong A (dimensionConstant (Fintype.card ι))
      (dimensionConstant_nonneg _) hlt hr
    linarith
  · intro hu
    rw [hu, uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
    ring


end MathAndTheory.Gyires.Exceptional
