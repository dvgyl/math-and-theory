module

public import RootBound
public import TransferBlocks
public import SharpTail

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCycle

open Matrix Equiv
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.PermutationTransfer
open MathAndTheory.Gyires.GramTransfer

theorem cycle_scale_square_le_permanent_square (n : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    weightScale a b c ^ (2*n) ≤ (polynomialMatrix (finRotate n) a b c).permanent^2 := by
  have hnonneg := pow_nonneg (weightScale_properties ha hb hc).1 n
  have hbound := cycle_weightScale_lower_bound n ha hb hc
  have hsquare := pow_le_pow_left₀ hnonneg hbound 2
  simpa only [← pow_mul, Nat.mul_comm n 2] using hsquare

theorem cycle_left_gram_inequality (n : ℕ) (hn : 48 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    dimensionConstant n *
      (polynomialMatrix (finRotate n) a b c *
        (polynomialMatrix (finRotate n) a b c).transpose).permanent ≤
      (polynomialMatrix (finRotate n) a b c).permanent^2 := by
  have htrace : dimensionConstant n *
      (polynomialMatrix (finRotate n) a b c *
        (polynomialMatrix (finRotate n) a b c).transpose).permanent ≤
      weightScale a b c ^ (2*n) := by
    cases n with
    | zero => omega
    | succ n =>
      rw [gram_permanent_transfer_formula]
      exact PermutationTransfer.Sharp.transfer_tail_bound ha hb hc (n+1) hn
  exact htrace.trans (cycle_scale_square_le_permanent_square n ha hb hc)

theorem cycle_right_gram_inequality (n : ℕ) (hn : 48 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    dimensionConstant n *
      ((polynomialMatrix (finRotate n) a b c).transpose *
        polynomialMatrix (finRotate n) a b c).permanent ≤
      (polynomialMatrix (finRotate n) a b c).permanent^2 := by
  rw [← polynomialMatrix_normal]
  exact cycle_left_gram_inequality n hn ha hb hc

theorem cycle_both_gram_inequalities (n : ℕ) (hn : 48 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := polynomialMatrix (finRotate n) a b c
    dimensionConstant n * (A * A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant n * (A.transpose * A).permanent ≤ A.permanent^2 := by
  exact ⟨cycle_left_gram_inequality n hn ha hb hc,
    cycle_right_gram_inequality n hn ha hb hc⟩

theorem cycle_left_gram_inequality_strict (n : ℕ) (hn : 48 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) :
    dimensionConstant n *
      (polynomialMatrix (finRotate n) a b c *
        (polynomialMatrix (finRotate n) a b c).transpose).permanent <
      (polynomialMatrix (finRotate n) a b c).permanent^2 := by
  have htrace : dimensionConstant n *
      (polynomialMatrix (finRotate n) a b c *
        (polynomialMatrix (finRotate n) a b c).transpose).permanent <
      weightScale a b c ^ (2*n) := by
    cases n with
    | zero => omega
    | succ n =>
      rw [gram_permanent_transfer_formula]
      exact PermutationTransfer.Sharp.transfer_tail_bound_strict ha hb hc hpositive (n+1) hn
  exact htrace.trans_le (cycle_scale_square_le_permanent_square n ha hb hc)

theorem cycle_right_gram_inequality_strict (n : ℕ) (hn : 48 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) :
    dimensionConstant n *
      ((polynomialMatrix (finRotate n) a b c).transpose *
        polynomialMatrix (finRotate n) a b c).permanent <
      (polynomialMatrix (finRotate n) a b c).permanent^2 := by
  rw [← polynomialMatrix_normal]
  exact cycle_left_gram_inequality_strict n hn ha hb hc hpositive

end MathAndTheory.Gyires.PermutationCycle
