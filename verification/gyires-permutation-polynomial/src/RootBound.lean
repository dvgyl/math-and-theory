module

public import BalancedWalks
public import MathAndTheory.Mathematics.Gyires.PermutationScale

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCycle

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.PermutationTransfer

theorem twoState_square (a b c : ℝ) :
    twoStateMatrix a b c ^ 2 =
      b • twoStateMatrix a b c + (a*c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoStateMatrix, pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem trace_recurrence_of_square {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℝ) (b d : ℝ) (hM : M^2 = b • M + d • (1 : Matrix κ κ ℝ))
    (n : ℕ) :
    Matrix.trace (M^(n+2)) =
      b * Matrix.trace (M^(n+1)) + d * Matrix.trace (M^n) := by
  have hpower : M^(n+2) = b • M^(n+1) + d • M^n := by
    rw [pow_add, hM, mul_add, mul_smul_comm, mul_smul_comm, mul_one, ← pow_succ]
  rw [hpower, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  rfl

theorem twoState_trace_recurrence (a b c : ℝ) (n : ℕ) :
    Matrix.trace (twoStateMatrix a b c ^ (n+2)) =
      b * Matrix.trace (twoStateMatrix a b c ^ (n+1)) +
        (a*c) * Matrix.trace (twoStateMatrix a b c ^ n) :=
  trace_recurrence_of_square _ b (a*c) (twoState_square a b c) n

def companionMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![b, a*c; 1, 0]

theorem companion_square (a b c : ℝ) :
    companionMatrix a b c ^ 2 =
      b • companionMatrix a b c + (a*c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companionMatrix, pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.add_apply, Matrix.smul_apply]

theorem companion_trace_eq (a b c : ℝ) (n : ℕ) :
    Matrix.trace (companionMatrix a b c ^ n) =
      Matrix.trace (twoStateMatrix a b c ^ n) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [Matrix.trace, companionMatrix, twoStateMatrix, Fin.sum_univ_succ]
  | more n hzero hone =>
    rw [trace_recurrence_of_square _ b (a*c) (companion_square a b c),
      twoState_trace_recurrence, hzero, hone]

noncomputable def negativeRoot (a b c : ℝ) : ℝ := b - positiveRoot a b c

theorem negativeRoot_formula (a b c : ℝ) :
    negativeRoot a b c = (b - Real.sqrt (b^2+4*a*c))/2 := by
  unfold negativeRoot positiveRoot
  ring

theorem roots_sum (a b c : ℝ) : positiveRoot a b c + negativeRoot a b c = b := by
  unfold negativeRoot
  ring

theorem negativeRoot_properties {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    negativeRoot a b c ≤ 0 ∧
      (negativeRoot a b c)^2 = b * negativeRoot a b c + a*c ∧
      |negativeRoot a b c| ≤ max a c := by
  obtain ⟨hLam0, hbLam, hLam⟩ := positiveRoot_properties ha hb hc
  have hMu0 : negativeRoot a b c ≤ 0 := by
    unfold negativeRoot
    linarith
  have hMu : (negativeRoot a b c)^2 = b * negativeRoot a b c + a*c := by
    unfold negativeRoot
    nlinarith
  have hmax0 : 0 ≤ max a c := ha.trans (le_max_left a c)
  have hac : a*c ≤ (max a c)^2 := by
    simpa [pow_two] using mul_le_mul (le_max_left a c) (le_max_right a c) hc hmax0
  have hbMu : b * negativeRoot a b c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hMu0
  refine ⟨hMu0, hMu, ?_⟩
  rw [abs_of_nonpos hMu0]
  nlinarith

theorem twoState_trace_eq_roots {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    Matrix.trace (twoStateMatrix a b c ^ n) =
      positiveRoot a b c ^ n + negativeRoot a b c ^ n := by
  have hLam := (positiveRoot_properties ha hb hc).2.2
  have hMu := (negativeRoot_properties ha hb hc).2.1
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Matrix.trace, Fin.sum_univ_succ]
  | one => simpa [Matrix.trace, twoStateMatrix, Fin.sum_univ_succ] using (roots_sum a b c).symm
  | more n hzero hone =>
    rw [twoState_trace_recurrence, hzero, hone]
    calc
      b * (positiveRoot a b c ^ (n+1) + negativeRoot a b c ^ (n+1)) +
          (a*c) * (positiveRoot a b c ^ n + negativeRoot a b c ^ n) =
          positiveRoot a b c ^ n * (positiveRoot a b c)^2 +
            negativeRoot a b c ^ n * (negativeRoot a b c)^2 := by
        rw [hLam, hMu]
        ring
      _ = positiveRoot a b c ^ (n+2) + negativeRoot a b c ^ (n+2) := by
        simp [pow_add]

theorem cycle_permanent_eq_roots (n : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (polynomialMatrix (finRotate (n+1)) a b c).permanent =
      a^(n+1) + c^(n+1) + positiveRoot a b c ^ (n+1) + negativeRoot a b c ^ (n+1) := by
  rw [cycle_permanent_formula, twoState_trace_eq_roots ha hb hc]
  ring

theorem cycle_positiveRoot_lower_bound (n : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    positiveRoot a b c ^ (n+1) ≤
      (polynomialMatrix (finRotate (n+1)) a b c).permanent := by
  have hMu := (negativeRoot_properties ha hb hc).2.2
  have habs : |negativeRoot a b c ^ (n+1)| ≤ (max a c)^(n+1) := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hMu _
  have hmax : (max a c)^(n+1) ≤ a^(n+1) + c^(n+1) := by
    rcases le_total a c with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg ha _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg hc _)
  have hneg := neg_abs_le (negativeRoot a b c ^ (n+1))
  rw [cycle_permanent_eq_roots n ha hb hc]
  linarith

theorem cycle_weightScale_lower_bound_succ (n : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    weightScale a b c ^ (n+1) ≤
      (polynomialMatrix (finRotate (n+1)) a b c).permanent := by
  have haBound : a^(n+1) ≤ (polynomialMatrix (finRotate (n+1)) a b c).permanent := by
    simpa [threeWeights] using
      polynomial_constant_label_lower_bound (finRotate (n+1)) ha hb hc (0 : Fin 3)
  have hcBound : c^(n+1) ≤ (polynomialMatrix (finRotate (n+1)) a b c).permanent := by
    simpa [threeWeights] using
      polynomial_constant_label_lower_bound (finRotate (n+1)) ha hb hc (2 : Fin 3)
  have hLamBound := cycle_positiveRoot_lower_bound n ha hb hc
  unfold weightScale
  rcases le_total c (positiveRoot a b c) with h | h
  · rw [max_eq_right h]
    rcases le_total a (positiveRoot a b c) with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  · rw [max_eq_left h]
    rcases le_total a c with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]

theorem cycle_weightScale_lower_bound (n : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    weightScale a b c ^ n ≤ (polynomialMatrix (finRotate n) a b c).permanent := by
  cases n with
  | zero => simp [Matrix.permanent_isEmpty]
  | succ n => exact cycle_weightScale_lower_bound_succ n ha hb hc

end MathAndTheory.Gyires.PermutationCycle
