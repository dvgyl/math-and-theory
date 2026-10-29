module

public import WeightedBernstein

@[expose] public section

namespace MathAndTheory.Gyires.PermutationWeightedConcrete

open Matrix Finset
open MathAndTheory.Gyires.PermutationTransfer
open MathAndTheory.Gyires.PermutationTransfer.Sharp
open scoped BigOperators Matrix

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem right_comparison_of_upper {d e f : ℝ}
    (hd : d ≤ upperD f) (he : e ≤ upperE f)
    (v : Fin 6 → ℝ) (hv : ∀ i, 0 < v i)
    (hupper : ∀ i, (transferTwo (upperD f) (upperE f) f *ᵥ v) i ≤ K*v i) :
    ∀ i, (transferTwo d e f *ᵥ v) i ≤ K*v i := by
  intro i
  calc
    _ ≤ (transferTwo (upperD f) (upperE f) f *ᵥ v) i := by
      simp only [Matrix.mulVec, dotProduct]
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (transferTwo_mono hd he i j) (hv j).le
    _ ≤ _ := hupper i

theorem weighted_energy_le_of_upper {d e f : ℝ}
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hf0 : 0 ≤ f)
    (hd : d ≤ upperD f) (he : e ≤ upperE f)
    (v : Fin 6 → ℝ) (hv : ∀ i, 0 < v i) :
    weightedEnergy (fun i => v (reflectIndex i)) v (transferTwo d e f ^ 2) ≤
      weightedEnergy (fun i => v (reflectIndex i)) v
        (transferTwo (upperD f) (upperE f) f ^ 2) := by
  have hr : 0 < v 2 / v 3 := div_pos (hv 2) (hv 3)
  rw [weightedEnergy_reflection v hv, weightedEnergy_reflection v hv,
    power_two_energy_eq _ _ _ _ (ne_of_gt hr), power_two_energy_eq _ _ _ _ (ne_of_gt hr)]
  exact power_two_energy_mono hd0 he0 hf0 hr hd he

theorem comparison_and_energy_of_upper {d e f : ℝ}
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hf0 : 0 ≤ f)
    (hd : d ≤ upperD f) (he : e ≤ upperE f)
    (v : Fin 6 → ℝ) (hv : ∀ i, 0 < v i)
    (hupper : ∀ i, (transferTwo (upperD f) (upperE f) f *ᵥ v) i ≤ K*v i)
    (henergy : weightedEnergy (fun i => v (reflectIndex i)) v
      (transferTwo (upperD f) (upperE f) f ^ 2) ≤ 39) :
    (∀ i, (transferTwo d e f *ᵥ v) i ≤ K*v i) ∧
    (∀ i, ((transferTwo d e f).transpose *ᵥ (fun j => v (reflectIndex j))) i ≤
      K*v (reflectIndex i)) ∧
    weightedEnergy (fun i => v (reflectIndex i)) v (transferTwo d e f ^ 2) ≤ 39 := by
  have hright := right_comparison_of_upper hd he v hv hupper
  refine ⟨hright, ?_, (weighted_energy_le_of_upper hd0 he0 hf0 hd he v hv).trans henergy⟩
  intro i
  rw [transpose_mulVec_reflect]
  exact hright (reflectIndex i)

theorem transferTwo_weighted_comparison {d e f : ℝ}
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hd : d ≤ upperD f) (he : e ≤ upperE f) :
    ∃ v : Fin 6 → ℝ, (∀ i, 0 < v i) ∧
      (∀ i, (transferTwo d e f *ᵥ v) i ≤ K*v i) ∧
      (∀ i, ((transferTwo d e f).transpose *ᵥ (fun j => v (reflectIndex j))) i ≤
        K*v (reflectIndex i)) ∧
      weightedEnergy (fun i => v (reflectIndex i)) v (transferTwo d e f ^ 2) ≤ 39 := by
  by_cases hzero : f = 0
  · subst f
    have hv : ∀ i, 0 < zeroVector i := by
      intro i
      fin_cases i <;> norm_num [zeroVector, K]
    refine ⟨zeroVector, hv, comparison_and_energy_of_upper hd0 he0 hf0 hd he _ hv ?_ ?_⟩
    · intro i
      fin_cases i <;>
        norm_num [upperD, upperE, transferTwo, zeroVector, K, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ]
    · have hr : 0 < zeroVector 2 / zeroVector 3 := div_pos (hv 2) (hv 3)
      rw [weightedEnergy_reflection _ hv, power_two_energy_eq _ _ _ _ (ne_of_gt hr)]
      norm_num [zeroVector, K, upperD, upperE, powerTwoEnergy, energyBase, energyLinear]
  by_cases hone : f = 1
  · subst f
    have hv : ∀ i, 0 < unitVector i := by
      intro i
      fin_cases i <;> norm_num [unitVector, K]
    refine ⟨unitVector, hv, comparison_and_energy_of_upper hd0 he0 hf0 hd he _ hv ?_ ?_⟩
    · intro i
      fin_cases i <;>
        norm_num [upperD, upperE, transferTwo, unitVector, K, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ]
    · have hr : 0 < unitVector 2 / unitVector 3 := div_pos (hv 2) (hv 3)
      rw [weightedEnergy_reflection _ hv, power_two_energy_eq _ _ _ _ (ne_of_gt hr)]
      norm_num [unitVector, K, upperD, upperE, powerTwoEnergy, energyBase, energyLinear]
  have hf : 0 < f := lt_of_le_of_ne hf0 (Ne.symm hzero)
  have hflt : f < 1 := lt_of_le_of_ne hf1 hone
  have hv := interiorVector_pos hf hflt
  refine ⟨interiorVector f, hv,
    comparison_and_energy_of_upper hd0 he0 hf0 hd he _ hv (interior_comparison hf hflt) ?_⟩
  have hr : 0 < interiorVector f 2 / interiorVector f 3 := div_pos (hv 2) (hv 3)
  rw [weightedEnergy_reflection _ hv, power_two_energy_eq _ _ _ _ (ne_of_gt hr),
    interior_ratio_eq hf hflt]
  exact upper_energy_bound hf hflt

end MathAndTheory.Gyires.PermutationWeightedConcrete
