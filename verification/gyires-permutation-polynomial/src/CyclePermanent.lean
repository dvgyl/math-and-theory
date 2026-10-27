module

public import LocalCurrent

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCycle

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationMatrixBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem centeredMap_eq_comp (p : Equiv.Perm ι) (d : ι → Fin 3) :
    centeredMap p d = p ∘ (fun i => polynomialSteps p (d i) i) := by
  funext i
  generalize hd : d i = k
  fin_cases k <;>
    simp [centeredMap, centeredSteps, polynomialSteps, hd,
      pow_two, Equiv.Perm.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem bijective_comp_perm_iff (p : Equiv.Perm ι) (f : ι → ι) :
    Function.Bijective (p ∘ f) ↔ Function.Bijective f := by
  constructor
  · intro h
    constructor
    · intro i j hij
      apply h.1
      exact congrArg p hij
    · intro j
      obtain ⟨i, hi⟩ := h.2 (p j)
      exact ⟨i, p.injective hi⟩
  · exact p.bijective.comp

theorem polynomial_permanent_eq_centered_sum (p : Equiv.Perm ι) (a b c : ℝ) :
    (polynomialMatrix p a b c).permanent =
      ∑ d : ι → Fin 3,
        if Function.Bijective (centeredMap p d)
        then ∏ i, threeWeights a b c (d i) else 0 := by
  rw [polynomial_permanent_eq_offset_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [centeredMap_eq_comp, bijective_comp_perm_iff]

omit [Fintype ι] [DecidableEq ι] in
theorem not_balanced_zero [Nonempty ι] (p : Equiv.Perm ι) :
    ¬ Balanced p (fun _ => 0) := by
  intro h
  let i : ι := Classical.choice inferInstance
  have hi := (h i).mp rfl
  norm_num at hi

omit [Fintype ι] [DecidableEq ι] in
theorem not_balanced_two [Nonempty ι] (p : Equiv.Perm ι) :
    ¬ Balanced p (fun _ => 2) := by
  intro h
  let i : ι := Classical.choice inferInstance
  have hi := (h i).mpr rfl
  norm_num at hi

omit [Fintype ι] [DecidableEq ι] in
theorem constant_zero_ne_two [Nonempty ι] :
    (fun _ : ι => (0 : Fin 3)) ≠ (fun _ => 2) := by
  intro h
  let i : ι := Classical.choice inferInstance
  have hi := congrFun h i
  norm_num at hi

theorem sum_bijective_classification [Nonempty ι]
    {R : Type*} [CommSemiring R] (p : Equiv.Perm ι)
    (hp : OneCycle p) (w : (ι → Fin 3) → R) :
    (∑ d : ι → Fin 3, if Function.Bijective (centeredMap p d) then w d else 0) =
      w (fun _ => 0) + w (fun _ => 2) +
      ∑ d : ι → Fin 3, if Balanced p d then w d else 0 := by
  classical
  have hterm (d : ι → Fin 3) :
      (if Function.Bijective (centeredMap p d) then w d else 0) =
        (if d = (fun _ => 0) then w d else 0) +
        (if d = (fun _ => 2) then w d else 0) +
        (if Balanced p d then w d else 0) := by
    have hclass : Function.Bijective (centeredMap p d) ↔
        d = (fun _ => 0) ∨ d = (fun _ => 2) ∨ Balanced p d := by
      rw [bijective_classification p d hp]
      simp only [funext_iff]
    simp only [hclass]
    by_cases hzero : d = (fun _ => 0)
    · subst d
      simp [constant_zero_ne_two, not_balanced_zero]
    · by_cases htwo : d = (fun _ => 2)
      · subst d
        simp [Ne.symm constant_zero_ne_two, not_balanced_two]
      · simp [hzero, htwo]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib]

noncomputable def balancedWeight (p : Equiv.Perm ι) (a b c : ℝ) : ℝ :=
  ∑ d : ι → Fin 3, if Balanced p d then ∏ i, threeWeights a b c (d i) else 0

theorem polynomial_permanent_eq_balanced [Nonempty ι] (p : Equiv.Perm ι)
    (hp : OneCycle p) (a b c : ℝ) :
    (polynomialMatrix p a b c).permanent =
      a ^ Fintype.card ι + c ^ Fintype.card ι + balancedWeight p a b c := by
  rw [polynomial_permanent_eq_centered_sum, sum_bijective_classification p hp]
  simp [balancedWeight, threeWeights]

end MathAndTheory.Gyires.PermutationCycle
