module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Definitions
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-!
# Doubly stochastic circulants

A circulant with nonnegative weights summing to one is doubly stochastic (`circ_nonneg`,
`circ_row_sum`, `circ_column_sum`), and the denominator of Gyires's ratio is then positive
(`positiveDenominator`).
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MathAndTheory.GyiresCirculant5

open scoped BigOperators

def gyiresDenominator (w : Fin 5 → ℝ) : ℝ :=
  (circ w * (circ w).transpose).permanent +
    ((circ w).transpose * circ w).permanent + 2 * (circ w * circ w).permanent

theorem circ_nonneg (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∀ i j, 0 ≤ circ w i j := by
  intro i j
  exact hw (j - i)

theorem circ_row_sum (w : Fin 5 → ℝ) (hsum : ∑ i, w i = 1) (i : Fin 5) :
    ∑ j, circ w i j = 1 := by
  let e : Equiv.Perm (Fin 5) :=
    { toFun := fun j => j - i
      invFun := fun j => j + i
      left_inv := by intro j; simp
      right_inv := by intro j; simp }
  change (∑ j, w (e j)) = 1
  exact (Equiv.sum_comp e w).trans hsum

theorem circ_column_sum (w : Fin 5 → ℝ) (hsum : ∑ i, w i = 1) (j : Fin 5) :
    ∑ i, circ w i j = 1 := by
  let e : Equiv.Perm (Fin 5) :=
    { toFun := fun i => j - i
      invFun := fun i => j - i
      left_inv := by intro i; exact sub_sub_cancel j i
      right_inv := by intro i; exact sub_sub_cancel j i }
  change (∑ i, w (e i)) = 1
  exact (Equiv.sum_comp e w).trans hsum

private theorem mul_entries_nonneg (M N : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hN : ∀ i j, 0 ≤ N i j) :
    ∀ i j, 0 ≤ (M * N) i j := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hM i k) (hN k j))

private theorem permanent_nonneg_of_entries (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) : 0 ≤ M.permanent := by
  unfold Matrix.permanent
  exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => hM (σ i) i))

private theorem permanent_pos_of_entries_and_diagonal (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hdiag : ∀ i, 0 < M i i) : 0 < M.permanent := by
  classical
  unfold Matrix.permanent
  apply Finset.sum_pos'
  · intro σ _
    exact Finset.prod_nonneg (fun i _ => hM (σ i) i)
  · refine ⟨Equiv.refl (Fin 5), Finset.mem_univ _, ?_⟩
    exact Finset.prod_pos (fun i _ => hdiag i)

theorem positiveDenominator (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : 0 < gyiresDenominator w := by
  classical
  have hM := circ_nonneg w hw
  have hMT : ∀ i j, 0 ≤ (circ w).transpose i j := fun i j => hM j i
  have hG := mul_entries_nonneg (circ w) (circ w).transpose hM hMT
  have hT := mul_entries_nonneg (circ w).transpose (circ w) hMT hM
  have hQ := mul_entries_nonneg (circ w) (circ w) hM hM
  have hsome : ∃ j, 0 < w j := by
    by_contra hn
    have hnonpos : ∀ i, w i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)
    have hs : (∑ i, w i) ≤ 0 := Finset.sum_nonpos (fun i _ => hnonpos i)
    linarith
  obtain ⟨j, hj⟩ := hsome
  have hdiag : ∀ i, 0 < (circ w * (circ w).transpose) i i := by
    intro i
    rw [Matrix.mul_apply]
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (hM i k) (hM i k)
    · refine ⟨i + j, Finset.mem_univ _, ?_⟩
      have hij : circ w i (i + j) = w j := by
        change w ((i + j) - i) = w j
        congr 1
        abel
      have hp : 0 < circ w i (i + j) := by rw [hij]; exact hj
      exact mul_pos hp hp
  have hgpos := permanent_pos_of_entries_and_diagonal _ hG hdiag
  have htnn := permanent_nonneg_of_entries _ hT
  have hqnn := permanent_nonneg_of_entries _ hQ
  unfold gyiresDenominator
  linarith

end MathAndTheory.GyiresCirculant5
