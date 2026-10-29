module
public import SequenceSemantics

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

/-- Zero coefficient polynomials are omitted, rather than assigned degree zero. -/
def filteredCharacteristic {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (P : ι → ℂ[X]) : ℂ[X] := by
  classical
  exact ∏ i : {i // P i ≠ 0}, (X - C (lam i)) ^ ((P i).natDegree + 1)

theorem expPoly_sum_filter_zero {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (P : ι → ℂ[X]) :
    (∑ i, expPoly (lam i) (P i)) =
      ∑ i : {i // P i ≠ 0}, expPoly (lam i) (P i) := by
  classical
  apply Finset.sum_congr_set {i | P i ≠ 0}
  · intro i hi
    rfl
  · intro i hi
    have hPi : P i = 0 := not_not.mp hi
    ext n
    simp [expPoly, hPi]

/-- Minimality remains exact when entire exponential bases disappear. -/
theorem minimalCharacteristic_expPoly_sum_allow_zero {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) :
    MinimalCharacteristic (filteredCharacteristic lam P) (∑ i, expPoly (lam i) (P i)) := by
  classical
  rw [expPoly_sum_filter_zero]
  exact minimalCharacteristic_expPoly_sum (fun i : {i // P i ≠ 0} => lam i)
    (fun i => hlam i) (hinj.comp Subtype.val_injective)
    (fun i => P i) (fun i => i.property)

/-- Exact recurrence rank with zero coefficients handled before the rank engine. -/
theorem recurrenceRank_expPoly_sum_allow_zero {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) :
    recurrenceRank (∑ i, expPoly (lam i) (P i)) =
      ∑ i, if P i = 0 then 0 else (P i).natDegree + 1 := by
  classical
  rw [expPoly_sum_filter_zero]
  rw [recurrenceRank_expPoly_sum (fun i : {i // P i ≠ 0} => lam i)
    (fun i => hlam i) (hinj.comp Subtype.val_injective) (fun i => P i) (fun i => i.property)]
  symm
  apply Finset.sum_congr_set {i | P i ≠ 0}
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    simp only [ite_eq_right hi]
  · intro i hi
    have hPi : P i = 0 := not_not.mp hi
    simp [hPi]

end PowerRank
