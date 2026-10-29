module

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathAndTheory.Gyires.PermutationMatrixBridge

open Matrix Finset Equiv
open scoped BigOperators

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def choiceMatrix [CommSemiring R] (step : κ → ι → ι) (weight : κ → R) :
    Matrix ι ι R :=
  fun row col => ∑ label, if step label col = row then weight label else 0

theorem permanent_choiceMatrix [CommSemiring R]
    (step : κ → ι → ι) (weight : κ → R) :
    (choiceMatrix step weight).permanent =
      ∑ labels : ι → κ,
        if Function.Bijective (fun i => step (labels i) i)
        then ∏ i, weight (labels i) else 0 := by
  classical
  unfold Matrix.permanent choiceMatrix
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro labels hlabels
  let f : ι → ι := fun i => step (labels i) i
  change (∑ σ : Equiv.Perm ι, ∏ i, if f i = σ i then weight (labels i) else 0) =
    if Function.Bijective f then ∏ i, weight (labels i) else 0
  by_cases hf : Function.Bijective f
  · rw [ite_eq_left hf]
    let σ : Equiv.Perm ι := Equiv.ofBijective f hf
    rw [Finset.sum_eq_single σ]
    · simp [σ]
    · intro τ hτ hne
      have hpoint : ∃ i, f i ≠ τ i := by
        by_contra h
        push Not at h
        apply hne
        apply Equiv.ext
        intro i
        exact (h i).symm
      obtain ⟨i, hi⟩ := hpoint
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    · intro h
      exact (h (Finset.mem_univ σ)).elim
  · rw [ite_eq_right hf]
    apply Finset.sum_eq_zero
    intro σ hσ
    have hpoint : ∃ i, f i ≠ σ i := by
      by_contra h
      push Not at h
      apply hf
      have heq : f = σ := funext h
      rw [heq]
      exact σ.bijective
    obtain ⟨i, hi⟩ := hpoint
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [Fintype ι] in
theorem choiceMatrix_eq_sum_permMatrix [CommSemiring R]
    (step : κ → Equiv.Perm ι) (weight : κ → R) :
    choiceMatrix (fun k => step k) weight =
      ∑ k, weight k • ((step k)⁻¹).permMatrix R := by
  classical
  ext row col
  simp only [choiceMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  by_cases h : step k col = row
  · have hinv : (step k).symm row = col := by
      apply (step k).injective
      simpa using h.symm
    simp [h, hinv]
  · have hinv : (step k).symm row ≠ col := by
      intro hinv
      apply h
      have := congrArg (step k) hinv
      simpa using this.symm
    simp [h, hinv]

theorem permanent_weighted_permutations [CommSemiring R]
    (step : κ → Equiv.Perm ι) (weight : κ → R) :
    (∑ k, weight k • ((step k)⁻¹).permMatrix R).permanent =
      ∑ labels : ι → κ,
        if Function.Bijective (fun i => step (labels i) i)
        then ∏ i, weight (labels i) else 0 := by
  rw [← choiceMatrix_eq_sum_permMatrix]
  exact permanent_choiceMatrix _ _

theorem choice_weight_power_le_permanent
    (step : κ → Equiv.Perm ι) (weight : κ → ℝ)
    (hweight : ∀ k, 0 ≤ weight k) (k : κ) :
    weight k ^ Fintype.card ι ≤ (choiceMatrix (fun j => step j) weight).permanent := by
  classical
  rw [permanent_choiceMatrix]
  have hnonneg : ∀ labels : ι → κ,
      0 ≤ if Function.Bijective (fun i => step (labels i) i)
          then ∏ i, weight (labels i) else 0 := by
    intro labels
    split
    · exact Finset.prod_nonneg fun i hi => hweight (labels i)
    · exact le_rfl
  have hterm := Finset.single_le_sum (fun labels _ => hnonneg labels)
    (Finset.mem_univ (fun _ : ι => k))
  simpa [(step k).bijective] using hterm

def threeWeights (a b c : ℝ) : Fin 3 → ℝ := ![a, b, c]

def polynomialSteps (p : Equiv.Perm ι) : Fin 3 → Equiv.Perm ι :=
  ![1, p⁻¹, (p⁻¹)^2]

noncomputable def polynomialMatrix (p : Equiv.Perm ι) (a b c : ℝ) : Matrix ι ι ℝ :=
  a • (1 : Matrix ι ι ℝ) + b • p.permMatrix ℝ + c • (p.permMatrix ℝ)^2

theorem choiceMatrix_polynomialSteps (p : Equiv.Perm ι) (a b c : ℝ) :
    choiceMatrix (fun k => polynomialSteps p k) (threeWeights a b c) =
      polynomialMatrix p a b c := by
  rw [choiceMatrix_eq_sum_permMatrix]
  simp [polynomialSteps, threeWeights, polynomialMatrix, Fin.sum_univ_succ,
    Matrix.permMatrix_mul, pow_two, add_assoc]

theorem polynomial_permanent_eq_offset_sum (p : Equiv.Perm ι) (a b c : ℝ) :
    (polynomialMatrix p a b c).permanent =
      ∑ labels : ι → Fin 3,
        if Function.Bijective (fun i => polynomialSteps p (labels i) i)
        then ∏ i, threeWeights a b c (labels i) else 0 := by
  rw [← choiceMatrix_polynomialSteps]
  exact permanent_choiceMatrix _ _

theorem polynomial_constant_label_lower_bound (p : Equiv.Perm ι)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (k : Fin 3) :
    threeWeights a b c k ^ Fintype.card ι ≤ (polynomialMatrix p a b c).permanent := by
  rw [← choiceMatrix_polynomialSteps]
  apply choice_weight_power_le_permanent
  intro j
  fin_cases j <;> simp [threeWeights, ha, hb, hc]

end MathAndTheory.Gyires.PermutationMatrixBridge
