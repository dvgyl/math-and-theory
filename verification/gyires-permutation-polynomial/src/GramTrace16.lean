module

public import FullTransfer
public import PermutationGramExpansion
public import Mathlib.Tactic.Abel

@[expose] public section

namespace MathAndTheory.Gyires.GramTransfer

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.PermutationCycle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fiveWeights (d e f : ℝ) : Fin 5 → ℝ := ![f, e, d, e, f]

def centeredSteps (p : Equiv.Perm ι) : Fin 5 → Equiv.Perm ι :=
  ![(p⁻¹)^2, p⁻¹, 1, p, p^2]

noncomputable def bandMatrix (p : Equiv.Perm ι) (d e f : ℝ) : Matrix ι ι ℝ :=
  d • (1 : Matrix ι ι ℝ) + e • shiftMatrix p (-1) + e • shiftMatrix p 1 +
    f • shiftMatrix p (-2) + f • shiftMatrix p 2

omit [Fintype ι] [DecidableEq ι] in
theorem centeredMap_eq_comp (p : Equiv.Perm ι) (d : ι → Fin 5) :
    (fun i => centeredSteps p (d i) i) = ((p⁻¹)^2 : Equiv.Perm ι) ∘ forwardMap p d := by
  funext i
  generalize hd : d i = k
  fin_cases k <;>
    simp [centeredSteps, forwardMap, forwardSteps, hd, pow_succ, Equiv.Perm.mul_apply]

omit [Fintype ι] in
theorem choiceMatrix_centeredSteps (p : Equiv.Perm ι) (d e f : ℝ) :
    choiceMatrix (fun k => centeredSteps p k) (fiveWeights d e f) = bandMatrix p d e f := by
  rw [choiceMatrix_eq_sum_permMatrix]
  simp [centeredSteps, fiveWeights, Fin.sum_univ_succ, bandMatrix, shiftMatrix]
  abel

theorem band_permanent_eq_forward (p : Equiv.Perm ι) (d e f : ℝ) :
    (bandMatrix p d e f).permanent =
      (choiceMatrix (fun k => forwardSteps p k) (fiveWeights d e f)).permanent := by
  rw [← choiceMatrix_centeredSteps, permanent_choiceMatrix, permanent_choiceMatrix]
  apply Finset.sum_congr rfl
  intro labels hlabels
  simp only [centeredMap_eq_comp, bijective_comp_perm_iff]
  rfl

theorem gram_eq_band (p : Equiv.Perm ι) (a b c : ℝ) :
    polynomialMatrix p a b c * (polynomialMatrix p a b c).transpose =
      bandMatrix p (a^2+b^2+c^2) (b*(a+c)) (a*c) := by
  rw [polynomialMatrix_gram]
  rfl

theorem gram_permanent_eq_fullTransfer (n : ℕ) (a b c : ℝ) :
    (polynomialMatrix (finRotate (n+1)) a b c *
      (polynomialMatrix (finRotate (n+1)) a b c).transpose).permanent =
      Matrix.trace (fullTransfer (fiveWeights (a^2+b^2+c^2) (b*(a+c)) (a*c)) ^ (n+1)) := by
  rw [gram_eq_band, band_permanent_eq_forward, forward_permanent_eq_trace]

end MathAndTheory.Gyires.GramTransfer
