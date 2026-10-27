module

public import MathAndTheory.Mathematics.Gyires.ExceptionalColumnBase
public import MathAndTheory.Mathematics.Gyires.ExceptionalCoefficients
public import MathAndTheory.Mathematics.Gyires.ExceptionalProbability

@[expose] public section

open scoped BigOperators
open Finset
open MathAndTheory.Gyires.Bernoulli

namespace MathAndTheory.Gyires.Exceptional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def exceptionalMatrix (u : ι → ℝ) (e : ι) : Matrix ι ι ℝ :=
  fun i j => if j = e then u i else (1-u i)/(Fintype.card ι-1 : ℕ)

lemma count_special (e : ι) : count (fun j => decide (j = e)) = 1 := by simp [count]

lemma rowMass_special (A : Matrix ι ι ℝ) (e : ι) :
    rowMass A (fun j => decide (j = e)) = fun i => A i e := by
  funext i
  simp [rowMass, Finset.sum_filter]

lemma exceptional_parameters (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) : (fun i => A i e) ∈ parameters 1 := by
  simpa only [rowMass_special, count_special, Nat.cast_one] using
    rowMass_mem_parameters A (fun j => decide (j = e)) hA

lemma exceptionalMatrix_eq_twoColumn (u : ι → ℝ) (e : ι) :
    exceptionalMatrix u e = twoColumn u (fun j => decide (j = e)) := by
  ext i j
  simp [exceptionalMatrix, twoColumn, count_special]

lemma eq_exceptionalMatrix (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (hn : 1 < Fintype.card ι) : A = exceptionalMatrix (fun i => A i e) e := by
  rw [exceptionalMatrix_eq_twoColumn]
  have h := eq_twoColumn_rowMass A (fun j => decide (j = e)) hA
    (exceptional_has_column_classes A e he) (by simp [count_special]) (by simpa [count_special] using hn)
  simpa only [rowMass_special] using h

lemma permanent_exceptionalMatrix (u : ι → ℝ) (e : ι) (k : ℕ)
    (hcard : Fintype.card ι = k+2) :
    (exceptionalMatrix u e).permanent = dimensionConstant (Fintype.card ι) *
      (oneSuccess u / (((k : ℝ)+1)/((k : ℝ)+2))^(k+1)) := by
  rw [exceptionalMatrix_eq_twoColumn, permanent_twoColumn u _
    (by simp [count_special]) (by simp [count_special, hcard]), count_special]
  simp only [referenceProbability, Nat.cast_one]
  change dimensionConstant (Fintype.card ι) *
    (probability u 1 / probability (fun _ : ι => 1/(Fintype.card ι : ℝ)) 1) = _
  rw [← oneSuccess_eq_probability, ← oneSuccess_eq_probability, oneSuccess_reference k hcard]

omit [DecidableEq ι] in
lemma exceptional_gram_columns (A : Matrix ι ι ℝ) (e : ι) (he : HasExceptionalColumn A e) :
    HasExceptionalColumn (A.transpose * A) e := by
  intro i j l hj hl
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [he r j l hj hl]

lemma exceptional_gram_parameter (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (k : ℕ) (hcard : Fintype.card ι = k+2) :
    (fun i => (A.transpose * A) i e) =
      specialParameters (secondMoment (fun i => A i e))
        ((1-secondMoment (fun i => A i e))/((k : ℝ)+1)) e := by
  have hshape := eq_exceptionalMatrix A e hA he (by omega : 1 < Fintype.card ι)
  have hsum := sum_col_of_mem_doublyStochastic hA e
  have hs : (∑ r, (1-A r e)*A r e) = 1-secondMoment (fun i => A i e) := by
    simp_rw [sub_mul, one_mul, ← pow_two]
    rw [Finset.sum_sub_distrib, hsum]
    rfl
  funext i
  by_cases hi : i = e
  · subst i
    simp [Matrix.mul_apply, Matrix.transpose_apply, specialParameters, secondMoment, pow_two]
  · have hentry (r : ι) : A r i = (1-A r e)/(Fintype.card ι-1 : ℕ) := by
      have hh := congrFun (congrFun hshape r) i
      simpa [exceptionalMatrix, hi] using hh
    simp only [Matrix.mul_apply, Matrix.transpose_apply, specialParameters, hi, ite_false]
    simp_rw [hentry, div_mul_eq_mul_div]
    rw [← Finset.sum_div, hs]
    simp [hcard]

lemma exceptional_permanent (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (k : ℕ) (hcard : Fintype.card ι = k+2) :
    A.permanent = dimensionConstant (Fintype.card ι) *
      (oneSuccess (fun i => A i e) / (((k : ℝ)+1)/((k : ℝ)+2))^(k+1)) := by
  have h := congrArg Matrix.permanent (eq_exceptionalMatrix A e hA he (by omega))
  rw [permanent_exceptionalMatrix _ _ k hcard] at h
  exact h

lemma exceptional_gram_permanent (A : Matrix ι ι ℝ) (e : ι)
    (hA : A ∈ doublyStochastic ℝ ι) (he : HasExceptionalColumn A e)
    (k : ℕ) (hcard : Fintype.card ι = k+2) :
    (A.transpose * A).permanent = dimensionConstant (Fintype.card ι) *
      (oneSuccess (specialParameters (secondMoment (fun i => A i e))
        ((1-secondMoment (fun i => A i e))/((k : ℝ)+1)) e) /
          (((k : ℝ)+1)/((k : ℝ)+2))^(k+1)) := by
  have hg : A.transpose * A ∈ doublyStochastic ℝ ι :=
    (doublyStochastic ℝ ι).mul_mem (transpose_mem_doublyStochastic_iff.mpr hA) hA
  rw [exceptional_permanent (A.transpose * A) e hg (exceptional_gram_columns A e he) k hcard,
    exceptional_gram_parameter A e hA he k hcard]


end MathAndTheory.Gyires.Exceptional
