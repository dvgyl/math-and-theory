import Research.DecisionTree
import Mathlib.Data.Fin.VecNotation

/-!
# A read-three counterexample with every query relevant

The four variables numbered 5,...,8 form `R`, their disjunction. The left
subtree computes `x ∧ y ∧ (¬u ∨ R)` and the right subtree computes
`x ∧ y ∧ (¬v ∨ R)`. The root chooses between these two subtrees. Every internal query is relevant, and no path repeats a
variable. The maximal total query multiplicity is three.
-/

set_option pp.maxSteps 2000

namespace ReadK
namespace Nonredundant

open Tree

/-- A single Boolean query. -/
def query (i : Fin 9) : Tree 9 := .node i (.leaf false) (.leaf true)

/-- The OR of four independent bits, whose probability of being false is 1/16. -/
def rareOr : Tree 9 :=
  .node 5 (.node 6 (.node 7 (.node 8 (.leaf false) (.leaf true))
    (.leaf true)) (.leaf true)) (.leaf true)

def left : Tree 9 :=
  .node 1 (.leaf false)
    (.node 3 (query 2) (.node 2 (.leaf false) rareOr))

def right : Tree 9 :=
  .node 2 (.leaf false)
    (.node 4 (query 1) (.node 1 (.leaf false) rareOr))

/-- The nine-variable witness. -/
def witness : Tree 9 := .node 0 left right

/-- At every internal node the two child subfunctions differ. -/
def Relevant {n : ℕ} : Tree n → Prop
  | .leaf _ => True
  | .node _ l r => l.eval ≠ r.eval ∧ Relevant l ∧ Relevant r

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem witness_regular : witness.Regular := by
  simp only [witness, left, right, query, rareOr, Tree.Regular]
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem witness_read_three : ∀ i, witness.count i ≤ 3 := by
  decide

theorem witness_counts : ∀ i, witness.count i = ![1, 3, 3, 1, 1, 2, 2, 2, 2] i := by
  decide

private theorem functions_ne_of_point {f g : BFun 9} (x : Cube 9)
    (h : f x ≠ g x) : f ≠ g := by
  intro he
  exact h (congrFun he x)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem witness_relevant : Relevant witness := by
  simp only [witness, left, right, query, rareOr, Relevant, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | (apply functions_ne_of_point (fun _ => false); decide)
    | (apply functions_ne_of_point (fun _ => true); decide)
    | (apply functions_ne_of_point
        ![false, true, true, false, true, false, false, false, false]; decide)

private theorem cov_const_left {n : ℕ} (b : Bool) (g : BFun n) :
    cov (fun _ => b) g = 0 := by
  simp [cov, mean, avg_const_mul]

private theorem cov_const_right {n : ℕ} (f : BFun n) (b : Bool) :
    cov f (fun _ => b) = 0 := by
  simp [cov, mean, avg_mul_const]

/-- The fair-branch recursion for a regular tree's expected sign. -/
private noncomputable def expectedLeaf {n : ℕ} : Tree n → ℝ
  | .leaf b => val b
  | .node _ l r => (expectedLeaf l + expectedLeaf r) / 2

private theorem mean_eq_expectedLeaf {n : ℕ} (t : Tree n) (ht : t.Regular) :
    mean t.eval = expectedLeaf t := by
  induction t with
  | leaf b => simp [Tree.eval, mean, expectedLeaf]
  | node j l r ihl ihr =>
      rcases ht with ⟨hl, hr, hlj, hrj⟩
      have hil := Tree.independent_of_count_zero l j hlj
      have hir := Tree.independent_of_count_zero r j hrj
      change avg (fun x => val (if x j then r.eval x else l.eval x)) = _
      calc
        _ = avg (fun x => if x j then val (r.eval x) else val (l.eval x)) := by
          apply avg_congr
          intro x
          cases h : x j <;> simp [h]
        _ = (mean l.eval + mean r.eval) / 2 := by
          exact avg_mux (fun x => val (l.eval x)) (fun x => val (r.eval x)) j
            (fun x => congrArg val (hil x)) (fun x => congrArg val (hir x))
        _ = expectedLeaf (.node j l r) := by
          rw [ihl hl, ihr hr]
          rfl

theorem witness_mean : mean witness.eval = -(33 : ℝ) / 64 := by
  rw [mean_eq_expectedLeaf witness witness_regular]
  norm_num [witness, left, right, query, rareOr, expectedLeaf, val]

theorem witness_variance : cov witness.eval witness.eval = (3007 : ℝ) / 4096 := by
  have hsq : avg (fun x => val (witness.eval x) * val (witness.eval x)) = 1 := by
    calc
      _ = avg (fun _ : Cube 9 => (1 : ℝ)) := by
        apply avg_congr
        intro x
        cases witness.eval x <;> norm_num [val]
      _ = 1 := avg_const _
  rw [cov, hsq, witness_mean]
  norm_num

private def eqUV : Tree 9 :=
  .node 3 (.node 4 (.leaf true) (.leaf false)) (query 4)

/-- A regular tree whose sign is the product of the two root child signs. -/
private def crossTree : Tree 9 :=
  .node 1 (.leaf true) (.node 2 (.leaf true)
    (.node 5 (.node 6 (.node 7 (.node 8 eqUV (.leaf true))
      (.leaf true)) (.leaf true)) (.leaf true)))

private theorem crossTree_regular : crossTree.Regular := by
  simp only [crossTree, eqUV, query, Tree.Regular]
  decide

private theorem sign_mul (b c : Bool) : val b * val c = val (b == c) := by
  cases b <;> cases c <;> norm_num [val]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem crossTree_eval : ∀ x, (left.eval x == right.eval x) = crossTree.eval x := by
  intro x
  cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;> cases h4 : x 4 <;>
    simp [left, right, query, rareOr, crossTree, eqUV, Tree.eval, h1, h2, h3, h4]

private theorem covariance_left_right : cov left.eval right.eval = (2943 : ℝ) / 4096 := by
  have hl : left.Regular := witness_regular.1
  have hr : right.Regular := witness_regular.2.1
  have hc : avg (fun x => val (left.eval x) * val (right.eval x)) = mean crossTree.eval := by
    apply avg_congr
    intro x
    rw [sign_mul, crossTree_eval]
  rw [cov, hc, mean_eq_expectedLeaf crossTree crossTree_regular,
    mean_eq_expectedLeaf left hl, mean_eq_expectedLeaf right hr]
  norm_num [crossTree, eqUV, left, right, rareOr, query, expectedLeaf, val]

private theorem covariance_query_gated (i : Fin 9) (hi : rareOr.count i = 0) :
    cov (query i).eval (Tree.node i (Tree.leaf false) rareOr).eval = (15 : ℝ) / 16 := by
  have hq : (query i).Regular := by simp [query, Tree.Regular, Tree.count]
  have hor : rareOr.Regular := by
    simp only [rareOr, Tree.Regular]
    decide
  have hg : (Tree.node i (Tree.leaf true) rareOr).Regular := by
    exact ⟨trivial, hor, rfl, hi⟩
  have hm : mean (query i).eval = 0 := by
    rw [mean_eq_expectedLeaf (query i) hq]
    norm_num [query, expectedLeaf, val]
  have hc : avg (fun x => val ((query i).eval x) *
      val ((Tree.node i (Tree.leaf false) rareOr).eval x)) =
      mean (Tree.node i (Tree.leaf true) rareOr).eval := by
    apply avg_congr
    intro x
    cases h : x i <;> simp [query, Tree.eval, h, val]
  rw [cov, hc, hm, zero_mul, sub_zero, mean_eq_expectedLeaf _ hg]
  norm_num [expectedLeaf, rareOr, val]

private theorem covariance_y_yOr :
    cov (query 2).eval (Tree.node 2 (Tree.leaf false) rareOr).eval = (15 : ℝ) / 16 :=
  covariance_query_gated 2 (by decide)

private theorem covariance_x_xOr :
    cov (query 1).eval (Tree.node 1 (Tree.leaf false) rareOr).eval = (15 : ℝ) / 16 :=
  covariance_query_gated 1 (by decide)

private theorem query_covariance (i : Fin 9) : (query i).covariance = 0 := by
  simp [query, Tree.covariance, Tree.eval, cov_const_left]

private theorem rareOr_covariance : rareOr.covariance = 0 := by
  simp [rareOr, Tree.covariance, Tree.eval, cov_const_left, cov_const_right]

private theorem gated_covariance (i : Fin 9) :
    (Tree.node i (Tree.leaf false) rareOr).covariance = 0 := by
  simp [Tree.covariance, Tree.eval, rareOr_covariance, cov_const_left]

private theorem left_covariance : left.covariance = (15 : ℝ) / 32 := by
  have hu : (Tree.node 3 (query 2) (Tree.node 2 (Tree.leaf false) rareOr)).covariance =
      (15 : ℝ) / 16 := by
    change cov (query 2).eval (Tree.node 2 (Tree.leaf false) rareOr).eval +
      ((query 2).covariance + (Tree.node 2 (Tree.leaf false) rareOr).covariance) / 2 = _
    rw [covariance_y_yOr, query_covariance, gated_covariance]
    norm_num
  change cov (fun _ : Cube 9 => false)
      (Tree.node 3 (query 2) (Tree.node 2 (Tree.leaf false) rareOr)).eval +
    (0 + (Tree.node 3 (query 2) (Tree.node 2 (Tree.leaf false) rareOr)).covariance) / 2 = _
  rw [cov_const_left, hu]
  norm_num

private theorem right_covariance : right.covariance = (15 : ℝ) / 32 := by
  have hv : (Tree.node 4 (query 1) (Tree.node 1 (Tree.leaf false) rareOr)).covariance =
      (15 : ℝ) / 16 := by
    change cov (query 1).eval (Tree.node 1 (Tree.leaf false) rareOr).eval +
      ((query 1).covariance + (Tree.node 1 (Tree.leaf false) rareOr).covariance) / 2 = _
    rw [covariance_x_xOr, query_covariance, gated_covariance]
    norm_num
  change cov (fun _ : Cube 9 => false)
      (Tree.node 4 (query 1) (Tree.node 1 (Tree.leaf false) rareOr)).eval +
    (0 + (Tree.node 4 (query 1) (Tree.node 1 (Tree.leaf false) rareOr)).covariance) / 2 = _
  rw [cov_const_left, hv]
  norm_num

/-- Exact total covariance of the nonredundant read-three tree. -/
theorem witness_covariance : witness.covariance = (4863 : ℝ) / 4096 := by
  change cov left.eval right.eval + (left.covariance + right.covariance) / 2 = _
  rw [covariance_left_right, left_covariance, right_covariance]
  norm_num

/-- An elementary exact logarithm bound, using 3^5 = 243 < 256 = 2^8. -/
theorem logCount_three_lt_eight_fifths : logCount 3 < (8 : ℝ) / 5 := by
  have h : Real.log ((3 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8) := by
    apply Real.log_lt_log (by norm_num)
    norm_num
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [logCount_of_pos (by norm_num : 0 < (3 : ℕ))]
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  nlinarith

/-- The variance-normalized logarithmic bound fails even for a nonredundant tree. -/
theorem violates_log_variance :
    logCount 3 * cov witness.eval witness.eval < witness.covariance := by
  rw [witness_variance, witness_covariance]
  have h := logCount_three_lt_eight_fifths
  nlinarith

end Nonredundant
end ReadK
