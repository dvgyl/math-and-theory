module

public import MathAndTheory.Mathematics.Gyires.TwoColumnContraction

/-!
This file proves the all-order four-block theorem for actual Mathlib doubly stochastic matrices.
The hypotheses count distinct row and column vectors. No block sizes or positive-entry condition are assumed.
The conclusions include the three contractions, the nonnegative margin, and equality exactly at the uniform matrix.
Orders zero and one and empty chosen classes are included by the two-column theorem.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace MathAndTheory.Gyires.Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def columnTypes (A : Matrix ι ι ℝ) : Finset (ι → ℝ) := by
  classical
  exact Finset.univ.image (fun j => fun i => A i j)

omit [DecidableEq ι] in
lemma column_mem_columnTypes (A : Matrix ι ι ℝ) (j : ι) :
    (fun i => A i j) ∈ columnTypes A := by
  classical
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

omit [DecidableEq ι] in
lemma exists_column_classes_of_card_le_two (A : Matrix ι ι ℝ)
    (hc : (columnTypes A).card ≤ 2) : ∃ c : ι → Bool, HasColumnClasses A c := by
  classical
  have hcard : Fintype.card (columnTypes A) ≤ Fintype.card Bool := by simpa using hc
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let v : ι → columnTypes A := fun j => ⟨(fun i => A i j), column_mem_columnTypes A j⟩
  refine ⟨fun j => e (v j), ?_⟩
  intro i j k h
  have hv : v j = v k := e.injective h
  exact congrFun (congrArg Subtype.val hv) i

/-- This theorem counts the actual distinct column vectors. -/
theorem two_column_bounds (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (hc : (columnTypes A).card ≤ 2) :
    (A * A.transpose).permanent ≤ A.permanent ∧
      dimensionConstant (Fintype.card ι) ≤ A.permanent ∧
      (A.permanent = dimensionConstant (Fintype.card ι) ↔ A = uniformMatrix) := by
  obtain ⟨c, hc'⟩ := exists_column_classes_of_card_le_two A hc
  exact column_class_bounds A c hA hc'

/-- All three permanent contractions hold with at most two row and column types. -/
theorem fourBlock_contractions (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hrow : (columnTypes A.transpose).card ≤ 2) (hcol : (columnTypes A).card ≤ 2) :
    (A * A.transpose).permanent ≤ A.permanent ∧
      (A.transpose * A).permanent ≤ A.permanent ∧ (A * A).permanent ≤ A.permanent := by
  have hl := (two_column_bounds A hA hcol).1
  have hr := (two_column_bounds A.transpose (transpose_mem_doublyStochastic_iff.mpr hA) hrow).1
  simp only [Matrix.transpose_transpose, Matrix.permanent_transpose] at hr
  have hs := MathAndTheory.GyiresCirculant5.PermanentGram.permanent_square_bound_of_gram_bounds
    A 1 A.permanent (by norm_num) (by simpa only [one_mul] using hl) (by simpa only [one_mul] using hr)
  exact ⟨hl, hr, by simpa only [one_mul] using hs⟩

/-- The four-block theorem gives the stated nonnegative margin in every finite order. -/
theorem fourBlock_margin (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hrow : (columnTypes A.transpose).card ≤ 2) (hcol : (columnTypes A).card ≤ 2) :
    4 * A.permanent * (A.permanent - dimensionConstant (Fintype.card ι)) ≤
      4 * A.permanent ^ 2 - dimensionConstant (Fintype.card ι) *
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ∧
    0 ≤ 4 * A.permanent * (A.permanent - dimensionConstant (Fintype.card ι)) := by
  obtain ⟨hl, hr, hs⟩ := fourBlock_contractions A hA hrow hcol
  have hd := (two_column_bounds A hA hcol).2.1
  have hc := dimensionConstant_nonneg (Fintype.card ι)
  have hsum : (A * A.transpose).permanent + (A.transpose * A).permanent +
      2 * (A * A).permanent ≤ 4 * A.permanent := by linarith
  refine ⟨?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hsum hc
    nlinarith [h]
  · exact mul_nonneg (mul_nonneg (by norm_num) (hc.trans hd)) (sub_nonneg.mpr hd)

/-- Gyires's inequality holds for every doubly stochastic matrix with these row and column counts. -/
theorem fourBlock_gyires (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hrow : (columnTypes A.transpose).card ≤ 2) (hcol : (columnTypes A).card ≤ 2) :
    dimensionConstant (Fintype.card ι) *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤
        4 * A.permanent ^ 2 := by
  have h := fourBlock_margin A hA hrow hcol
  linarith [h.1, h.2]

/-- Equality in Gyires's inequality holds exactly at the uniform matrix. -/
theorem fourBlock_gyires_eq_iff (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hrow : (columnTypes A.transpose).card ≤ 2) (hcol : (columnTypes A).card ≤ 2) :
    dimensionConstant (Fintype.card ι) *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
        4 * A.permanent ^ 2 ↔ A = uniformMatrix := by
  constructor
  · intro heq
    have hbounds := two_column_bounds A hA hcol
    apply hbounds.2.2.mp
    have hmargin := (fourBlock_margin A hA hrow hcol).1
    have hc := dimensionConstant_pos_all (Fintype.card ι)
    have hd : 0 < A.permanent := hc.trans_le hbounds.2.1
    by_contra hne
    have hstrict : dimensionConstant (Fintype.card ι) < A.permanent :=
      lt_of_le_of_ne hbounds.2.1 (Ne.symm hne)
    have hpositive : 0 < 4 * A.permanent * (A.permanent - dimensionConstant (Fintype.card ι)) := by
      exact mul_pos (mul_pos (by norm_num) hd) (sub_pos.mpr hstrict)
    linarith [hmargin]
  · intro heq
    rw [heq, uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
    ring


end MathAndTheory.Gyires.Bernoulli
