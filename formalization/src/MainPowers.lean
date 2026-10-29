module
public import GeneratorEvaluation
public import ZeroComponents
public import LayerMultiplicity
public import PowerBases

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

def mainPowerSequence (M : ℕ) : Seq := fun n => mainSequence n ^ M

def powerCoefficient (M : ℕ) (i : PowerIndex M) : ℂ[X] :=
  complexLayerPolynomial M i.1.val i.2.val

def powerCharacteristic (M : ℕ) : ℂ[X] :=
  ∏ i : PowerIndex M,
    (X - C (powerBase M i)) ^ expectedMultiplicity M i.1.val i.2.val

theorem mainPowerSequence_expansion (M : ℕ) :
    mainPowerSequence M = ∑ i : PowerIndex M, expPoly (powerBase M i) (powerCoefficient M i) := by
  ext n
  simp only [mainPowerSequence, Finset.sum_apply, Fintype.sum_sigma,
    powerBase, powerCoefficient]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ∑ k : Fin (M + j + 1),
      expPoly ((2 : ℂ) ^ k.val * (3 : ℂ) ^ j) (complexLayerPolynomial M j k.val) n)
    (2 * M + 1)]
  have h := mainSequence_power_expansion M n
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => expPoly ((2 : ℂ) ^ k * (3 : ℂ) ^ j) (complexLayerPolynomial M j k) n)
    (M + j + 1)

theorem complexLayer_multiplicity (M j k : ℕ) :
    (if complexLayerPolynomial M j k = 0 then 0 else
      (complexLayerPolynomial M j k).natDegree + 1) = layerMultiplicity M j k := by
  classical
  simp only [complexLayerPolynomial, Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective,
    natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective, layerMultiplicity]

theorem powerCoefficient_multiplicity (M : ℕ) (i : PowerIndex M) :
    (if powerCoefficient M i = 0 then 0 else (powerCoefficient M i).natDegree + 1) =
      expectedMultiplicity M i.1.val i.2.val := by
  classical
  change (if complexLayerPolynomial M i.1.val i.2.val = 0 then 0 else
    (complexLayerPolynomial M i.1.val i.2.val).natDegree + 1) = _
  rw [complexLayer_multiplicity,
    layerMultiplicity_eq_expected M i.1.val i.2.val (by omega) (by omega)]

theorem filteredCharacteristic_eq_product {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (P : ι → ℂ[X]) :
    filteredCharacteristic lam P =
      ∏ i, (X - C (lam i)) ^ (if P i = 0 then 0 else (P i).natDegree + 1) := by
  classical
  symm
  apply Finset.prod_congr_set {i | P i ≠ 0}
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    simp only [ite_eq_right hi]
  · intro i hi
    have hPi : P i = 0 := not_not.mp hi
    simp [hPi]

theorem powerCharacteristic_eq_filtered (M : ℕ) :
    powerCharacteristic M = filteredCharacteristic (powerBase M) (powerCoefficient M) := by
  classical
  rw [filteredCharacteristic_eq_product]
  apply Finset.prod_congr rfl
  intro i hi
  rw [powerCoefficient_multiplicity]

/-- Every power has the full stated minimal complex characteristic polynomial. -/
theorem mainPower_minimalCharacteristic (M : ℕ) :
    MinimalCharacteristic (powerCharacteristic M) (mainPowerSequence M) := by
  rw [mainPowerSequence_expansion, powerCharacteristic_eq_filtered]
  exact minimalCharacteristic_expPoly_sum_allow_zero (powerBase M)
    (powerBase_ne_zero M) (powerBase_injective M) (powerCoefficient M)

/-- Exact rank sum, before the separate cubic and square-count simplification. -/
theorem mainPower_recurrenceRank_sum (M : ℕ) :
    recurrenceRank (mainPowerSequence M) =
      ∑ j ∈ Finset.range (2 * M + 1), ∑ k ∈ Finset.range (M + j + 1),
        expectedMultiplicity M j k := by
  classical
  rw [mainPowerSequence_expansion, recurrenceRank_expPoly_sum_allow_zero (powerBase M)
    (powerBase_ne_zero M) (powerBase_injective M)]
  simp_rw [powerCoefficient_multiplicity]
  rw [Fintype.sum_sigma]
  change (∑ j : Fin (2 * M + 1), ∑ k : Fin (M + j.val + 1),
    expectedMultiplicity M j.val k.val) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ∑ k : Fin (M + j + 1), expectedMultiplicity M j k.val) (2 * M + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  exact Fin.sum_univ_eq_sum_range _ _

/-- The displayed minimal recurrence is valid from n=0 for every power. -/
theorem mainPower_annihilates_all_indices (M n : ℕ) :
    polyAction (powerCharacteristic M) (mainPowerSequence M) n = 0 := by
  have h := polyAction_sum_eq_zero_of_eventually (powerBase M) (powerBase_ne_zero M)
    (powerBase_injective M) (powerCoefficient M) (powerCharacteristic M)
    (by rw [← mainPowerSequence_expansion]; exact (mainPower_minimalCharacteristic M).1.2.2)
  rw [← mainPowerSequence_expansion] at h
  exact congrFun h n

end PowerRank
