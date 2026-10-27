module

public import MathAndTheory.Mathematics.Gyires.ExceptionalVector
public import MathAndTheory.Mathematics.GyiresCirculant5.Remarks
public import Mathlib.Tactic.FinCases

@[expose] public section

open scoped BigOperators
open MathAndTheory.Gyires MathAndTheory.Gyires.Bernoulli MathAndTheory.Gyires.Exceptional

namespace MathAndTheory.Gyires.ExceptionalExamples

noncomputable def parameter (t : ℝ) (i : Fin 3) : ℝ :=
  if i=0 then t else if i=1 then 1/3 else 2/3-t

noncomputable def probe (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := exceptionalMatrix (parameter t) 0

lemma probe_doublyStochastic (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2/3)) :
    probe t ∈ doublyStochastic ℝ (Fin 3) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [probe, exceptionalMatrix, parameter] <;> linarith [ht.1, ht.2]
  · intro i
    fin_cases i <;> simp [probe, exceptionalMatrix, parameter, Fin.sum_univ_three] <;> ring
  · intro j
    fin_cases j <;> simp [probe, exceptionalMatrix, parameter, Fin.sum_univ_three] <;> ring

lemma probe_exceptional (t : ℝ) : HasExceptionalColumn (probe t) 0 := by
  intro i j k hj hk
  simp [probe, exceptionalMatrix, hj, hk]

lemma probe_high_variance : secondMoment (parameter 0) = 5/9 := by
  norm_num [secondMoment, parameter, Fin.sum_univ_three]

lemma probe_low_variance : secondMoment (parameter (1/6)) = 7/18 := by
  norm_num [secondMoment, parameter, Fin.sum_univ_three]

lemma probe_three_row_types : (columnTypes (probe 0).transpose).card = 3 := by
  classical
  have hinj : Function.Injective (fun i : Fin 3 => fun j => probe 0 i j) := by
    intro i j hij
    have h := congrFun hij 0
    fin_cases i <;> fin_cases j <;> norm_num [probe, exceptionalMatrix, parameter] at h
    all_goals rfl
  unfold columnTypes
  exact (Finset.card_image_of_injective _ hinj).trans (by simp)

lemma probe_permanent_zero : (probe 0).permanent = 5/18 := by
  rw [MathAndTheory.GyiresCirculant5.permanent_succ, Fin.sum_univ_three]
  norm_num [Fin.sum_univ_three, MathAndTheory.GyiresCirculant5.permanent_fin_two,
    probe, exceptionalMatrix, parameter, Matrix.submatrix_apply, Equiv.swap_apply_def]

lemma probe_permanent_sixth : (probe (1/6)).permanent = 17/72 := by
  rw [MathAndTheory.GyiresCirculant5.permanent_succ, Fin.sum_univ_three]
  norm_num [Fin.sum_univ_three, MathAndTheory.GyiresCirculant5.permanent_fin_two,
    probe, exceptionalMatrix, parameter, Matrix.submatrix_apply, Equiv.swap_apply_def]

lemma probe_uniform : probe (1/3) = uniformMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [probe, exceptionalMatrix, parameter, uniformMatrix]

lemma probe_not_uniform_zero : probe 0 ≠ uniformMatrix := by
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [probe, exceptionalMatrix, parameter, uniformMatrix] at he

lemma probe_strict_zero : dimensionConstant 3 *
    ((probe 0 * (probe 0).transpose).permanent + ((probe 0).transpose * probe 0).permanent +
      2*(probe 0 * probe 0).permanent) < 4*(probe 0).permanent^2 := by
  have hA := probe_doublyStochastic 0 (by norm_num)
  have he : HasExceptionalVector (probe 0) := Or.inl ⟨0, probe_exceptional 0⟩
  have hi := exceptional_vector_gyires (probe 0) hA he (by norm_num)
  have heq := exceptional_vector_gyires_eq_iff (probe 0) hA he (by norm_num)
  exact lt_of_le_of_ne hi (fun h => probe_not_uniform_zero (heq.mp h))

example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2/3)) :
    dimensionConstant 3 * ((probe t).transpose * probe t).permanent ≤ (probe t).permanent^2 :=
  (exceptional_vector_strong (probe t) (probe_doublyStochastic t ht)
    (Or.inl ⟨0, probe_exceptional t⟩) (by norm_num)).2

example : dimensionConstant 3 *
    (((probe (1/6)).transpose * probe (1/6)).permanent +
      (probe (1/6) * (probe (1/6)).transpose).permanent +
      2*((probe (1/6)).transpose * (probe (1/6)).transpose).permanent) ≤
        4*((probe (1/6)).transpose).permanent^2 := by
  have hA := transpose_mem_doublyStochastic_iff.mpr (probe_doublyStochastic (1/6) (by norm_num))
  have he : HasExceptionalVector (probe (1/6)).transpose :=
    Or.inr ⟨0, by simpa only [Matrix.transpose_transpose] using probe_exceptional (1/6)⟩
  simpa only [Matrix.transpose_transpose, Fintype.card_fin] using exceptional_vector_gyires _ hA he (by norm_num)

example (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 2)) :
    dimensionConstant 2 * (A.transpose*A).permanent ≤ A.permanent^2 := by
  have he : HasExceptionalColumn A 0 := by
    intro i j k hj hk
    fin_cases j <;> fin_cases k <;> simp_all
  exact (exceptional_vector_strong A hA (Or.inl ⟨0, he⟩) (by norm_num)).2

noncomputable def deterministic : Matrix (Fin 3) (Fin 3) ℝ :=
  exceptionalMatrix (fun i => if i=0 then 1 else 0) 0

lemma deterministic_doublyStochastic : deterministic ∈ doublyStochastic ℝ (Fin 3) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [deterministic, exceptionalMatrix]
  · intro i
    fin_cases i <;> norm_num [deterministic, exceptionalMatrix, Fin.sum_univ_three]
  · intro j
    fin_cases j <;> norm_num [deterministic, exceptionalMatrix, Fin.sum_univ_three]

lemma deterministic_strong : dimensionConstant 3 *
    (deterministic.transpose*deterministic).permanent ≤ deterministic.permanent^2 := by
  have he : HasExceptionalColumn deterministic 0 := by
    intro i j k hj hk
    simp [deterministic, exceptionalMatrix, hj, hk]
  exact (exceptional_vector_strong deterministic deterministic_doublyStochastic
    (Or.inl ⟨0, he⟩) (by norm_num)).2

lemma uniform_equality : dimensionConstant 3 *
    ((probe (1/3)*(probe (1/3)).transpose).permanent +
      ((probe (1/3)).transpose*probe (1/3)).permanent +
      2*(probe (1/3)*probe (1/3)).permanent) = 4*(probe (1/3)).permanent^2 := by
  exact (exceptional_vector_gyires_eq_iff (probe (1/3))
    (probe_doublyStochastic (1/3) (by norm_num)) (Or.inl ⟨0, probe_exceptional (1/3)⟩)
    (by norm_num)).mpr probe_uniform


end MathAndTheory.Gyires.ExceptionalExamples
