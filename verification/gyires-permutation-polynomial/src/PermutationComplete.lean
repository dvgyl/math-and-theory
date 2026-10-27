module

public import SmallCycleBounds
public import PrototypeCoverage
public import OrderFourGap
public import GapFive
public import GapSix
public import Gap007
public import Gap008
public import Gap009
public import Gap010
public import Gap011
public import Gap012
public import Gap013
public import Gap014
public import Gap015
public import Gap016
public import Gap017
public import Gap018
public import Gap019
public import Gap020
public import Gap021
public import Gap022
public import CycleTailTwentyThree
public import CycleAssembly
public import PermanentCauchySchwarz

@[expose] public section

namespace MathAndTheory.Gyires.PermutationComplete

open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.PermutationCycle
open MathAndTheory.Gyires.PermutationCoefficients
open MathAndTheory.Gyires.PermutationCoefficientStage
open MathAndTheory.Gyires.PermutationAssembly
open MathAndTheory.GyiresCirculant5.PermanentGram

theorem cycle_all_gram_bounds (n : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := polynomialMatrix (finRotate n) a b c
    dimensionConstant n * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant n * (A.transpose*A).permanent ≤ A.permanent^2 := by
  by_cases hsmall : n ≤ 2
  · exact cycle_small_order_both_gram n hsmall a b c
  by_cases hlarge : 23 ≤ n
  · exact ThresholdTwentyThree.cycle_both_gram_inequalities n hlarge ha hb hc
  have hlo : 3 ≤ n := by omega
  have hhi : n ≤ 22 := by omega
  interval_cases n
  · exact cycle_order_three_both_gram ha hb hc
  · exact cycle_order_four_both_gram ha hb hc
  · exact cycle_order_five_both_gram ha hb hc
  · exact cycle_order_six_both_gram ha hb hc
  · exact cycle_order_007_both_gram ha hb hc
  · exact cycle_order_008_both_gram ha hb hc
  · exact cycle_order_009_both_gram ha hb hc
  · exact cycle_order_010_both_gram ha hb hc
  · exact cycle_order_011_both_gram ha hb hc
  · exact cycle_order_012_both_gram ha hb hc
  · exact cycle_order_013_both_gram ha hb hc
  · exact cycle_order_014_both_gram ha hb hc
  · exact cycle_order_015_both_gram ha hb hc
  · exact cycle_order_016_both_gram ha hb hc
  · exact cycle_order_017_both_gram ha hb hc
  · exact cycle_order_018_both_gram ha hb hc
  · exact cycle_order_019_both_gram ha hb hc
  · exact cycle_order_020_both_gram ha hb hc
  · exact cycle_order_021_both_gram ha hb hc
  · exact cycle_order_022_both_gram ha hb hc

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem permutation_polynomial_gram_bounds (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := polynomialMatrix p a b c
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant (Fintype.card ι) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  exact permutation_both_gram_of_positive_cycle_bounds p ha hb hc
    (fun n _ => (cycle_all_gram_bounds n ha hb hc).1)

theorem permutation_polynomial_square_bound (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := polynomialMatrix p a b c
    dimensionConstant (Fintype.card ι) * (A*A).permanent ≤ A.permanent^2 := by
  have h := permutation_polynomial_gram_bounds p ha hb hc
  exact permanent_square_bound_of_gram_bounds _ _ _ (dimensionConstant_nonneg _) h.1 h.2

theorem permutation_polynomial_gyires_bound (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := polynomialMatrix p a b c
    dimensionConstant (Fintype.card ι) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent)
      ≤ 4*A.permanent^2 := by
  have hg := permutation_polynomial_gram_bounds p ha hb hc
  have hs := permutation_polynomial_square_bound p ha hb hc
  dsimp only at hg hs ⊢
  nlinarith [hg.1, hg.2]

theorem cycle_strict_square_bound (n : ℕ) (hn : 23 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) :
    let A := polynomialMatrix (finRotate n) a b c
    dimensionConstant n * (A*A).permanent < A.permanent^2 := by
  have hl := ThresholdTwentyThree.cycle_left_gram_inequality_strict n hn ha hb hc hpositive
  have hr := ThresholdTwentyThree.cycle_right_gram_inequality n hn ha hb hc
  exact permanent_square_lt_of_gram_bounds _ _ _ (dimensionConstant_nonneg n) hl hr

theorem cycle_strict_gyires_bound (n : ℕ) (hn : 23 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) :
    let A := polynomialMatrix (finRotate n) a b c
    dimensionConstant n *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent)
      < 4*A.permanent^2 := by
  have hl := ThresholdTwentyThree.cycle_left_gram_inequality_strict n hn ha hb hc hpositive
  have hr := ThresholdTwentyThree.cycle_right_gram_inequality n hn ha hb hc
  exact gyires_lt_of_strong _ _ (dimensionConstant_nonneg n) hl hr

end MathAndTheory.Gyires.PermutationComplete
