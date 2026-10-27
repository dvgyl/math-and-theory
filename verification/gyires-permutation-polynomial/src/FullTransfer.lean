module

public import FiveOffsetStates
public import BalancedWalks

@[expose] public section

namespace MathAndTheory.Gyires.GramTransfer

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.PermutationCycle

noncomputable def fullTransfer (weight : Fin 5 → ℝ) : Matrix State State ℝ :=
  fun s t => ∑ k, if Transition s t k then weight k else 0

theorem fullTransfer_closed_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Equiv.Perm ι) (weight : Fin 5 → ℝ) :
    (∑ s : ι → State, ∏ i, fullTransfer weight (s i) (s (p i))) =
      ∑ d : ι → Fin 5,
        if Function.Bijective (forwardMap p d) then ∏ i, weight (d i) else 0 := by
  classical
  unfold fullTransfer
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hb : Function.Bijective (forwardMap p d)
  · rw [ite_eq_left hb, Finset.sum_eq_single (canonicalState p d)]
    · apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_left (canonicalState_transition p d hb i)
    · intro s hs hne
      have hpoint : ∃ i, ¬ Transition (s i) (s (p i)) (d i) := by
        by_contra h
        push Not at h
        exact hne (transition_unique p d s h)
      obtain ⟨i, hi⟩ := hpoint
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro s hs
    have hpoint : ∃ i, ¬ Transition (s i) (s (p i)) (d i) := by
      by_contra h
      push Not at h
      exact hb (transition_bijective p d s h)
    obtain ⟨i, hi⟩ := hpoint
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem forward_permanent_eq_trace (n : ℕ) (weight : Fin 5 → ℝ) :
    (choiceMatrix (fun k => forwardSteps (finRotate (n+1)) k) weight).permanent =
      Matrix.trace (fullTransfer weight ^ (n+1)) := by
  rw [trace_pow_eq_closed_walks, fullTransfer_closed_sum]
  exact permanent_choiceMatrix _ _

end MathAndTheory.Gyires.GramTransfer
