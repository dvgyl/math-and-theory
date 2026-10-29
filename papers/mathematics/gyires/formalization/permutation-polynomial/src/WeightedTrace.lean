module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathAndTheory.Gyires.WeightedTrace

open Matrix Finset
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι]

noncomputable def energy (ρ x : ι → ℝ) : ℝ := ∑ i, ρ i * x i ^ 2

noncomputable def frobenius (ρ : ι → ℝ) (A : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, (ρ i / ρ j) * A i j ^ 2

theorem frobenius_nonneg (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (A : Matrix ι ι ℝ) : 0 ≤ frobenius ρ A := by
  exact sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (div_nonneg (le_of_lt (hρ i)) (le_of_lt (hρ j))) (sq_nonneg _)

theorem row_cauchy (M : Matrix ι ι ℝ) (v x : ι → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i) (i : ι) :
    (∑ j, M i j * x j) ^ 2 ≤
      (∑ j, M i j * v j) * ∑ j, M i j * x j ^ 2 / v j := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _
    exact mul_nonneg (hM i j) (le_of_lt (hv j))
  · intro j _
    exact div_nonneg (mul_nonneg (hM i j) (sq_nonneg _)) (le_of_lt (hv j))
  · intro j _
    apply le_of_eq
    field_simp [ne_of_gt (hv j)]

theorem energy_contraction (M : Matrix ι ι ℝ) (u v x : ι → ℝ) (K : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hK : 0 ≤ K) (hr : ∀ i, ∑ j, M i j * v j ≤ K * v i)
    (hl : ∀ j, ∑ i, u i * M i j ≤ K * u j) :
    energy (fun i => u i / v i) (M *ᵥ x) ≤
      K ^ 2 * energy (fun i => u i / v i) x := by
  unfold energy
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ i, (u i / v i) * (∑ j, M i j * x j) ^ 2) ≤
        ∑ i, (u i / v i) * ((K * v i) * ∑ j, M i j * x j ^ 2 / v j) := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (le_of_lt (hu i)) (le_of_lt (hv i)))
      exact (row_cauchy M v x hM hv i).trans
        (mul_le_mul_of_nonneg_right (hr i) (sum_nonneg fun j _ =>
          div_nonneg (mul_nonneg (hM i j) (sq_nonneg _)) (le_of_lt (hv j))))
    _ = ∑ i, ∑ j, K * (x j ^ 2 / v j) * (u i * M i j) := by
      apply sum_congr rfl
      intro i _
      rw [← mul_assoc, Finset.mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp [ne_of_gt (hv i), ne_of_gt (hv j)]
    _ = ∑ j, K * (x j ^ 2 / v j) * (∑ i, u i * M i j) := by
      rw [sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ j, K * (x j ^ 2 / v j) * (K * u j) := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left (hl j)
      exact mul_nonneg hK (div_nonneg (sq_nonneg _) (le_of_lt (hv j)))
    _ = K ^ 2 * ∑ j, (u j / v j) * x j ^ 2 := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro j _
      ring

theorem frobenius_columns (ρ : ι → ℝ) (A : Matrix ι ι ℝ) :
    frobenius ρ A = ∑ j, (1 / ρ j) * energy ρ (fun i => A i j) := by
  unfold frobenius energy
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem frobenius_contraction (M A : Matrix ι ι ℝ) (u v : ι → ℝ) (K : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hK : 0 ≤ K) (hr : ∀ i, ∑ j, M i j * v j ≤ K * v i)
    (hl : ∀ j, ∑ i, u i * M i j ≤ K * u j) :
    frobenius (fun i => u i / v i) (M * A) ≤
      K ^ 2 * frobenius (fun i => u i / v i) A := by
  rw [frobenius_columns, frobenius_columns, Finset.mul_sum]
  apply sum_le_sum
  intro j _
  have he := energy_contraction M u v (fun i => A i j) K hM hu hv hK hr hl
  have hscale : 0 ≤ 1 / (u j / v j) := div_nonneg (by norm_num) (le_of_lt (div_pos (hu j) (hv j)))
  have h := mul_le_mul_of_nonneg_left he hscale
  simpa only [energy, Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_left_comm] using h

theorem frobenius_power_contraction [DecidableEq ι] (M A : Matrix ι ι ℝ) (u v : ι → ℝ) (K : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hK : 0 ≤ K) (hr : ∀ i, ∑ j, M i j * v j ≤ K * v i)
    (hl : ∀ j, ∑ i, u i * M i j ≤ K * u j) (k : ℕ) :
    frobenius (fun i => u i / v i) (M ^ k * A) ≤
      (K ^ 2) ^ k * frobenius (fun i => u i / v i) A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc]
    calc
      _ ≤ K ^ 2 * frobenius (fun i => u i / v i) (M ^ k * A) :=
        frobenius_contraction M (M ^ k * A) u v K hM hu hv hK hr hl
      _ ≤ K ^ 2 * ((K ^ 2) ^ k * frobenius (fun i => u i / v i) A) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by rw [pow_succ]; ring

theorem trace_product_sq (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (A B : Matrix ι ι ℝ) :
    Matrix.trace (A * B) ^ 2 ≤ frobenius ρ A * frobenius ρ B := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (ι × ι))
    (r := fun p => A p.1 p.2 * B p.2 p.1)
    (f := fun p => (ρ p.1 / ρ p.2) * A p.1 p.2 ^ 2)
    (g := fun p => (ρ p.2 / ρ p.1) * B p.2 p.1 ^ 2)
    (by intro p _; exact mul_nonneg (div_nonneg (le_of_lt (hρ _)) (le_of_lt (hρ _))) (sq_nonneg _))
    (by intro p _; exact mul_nonneg (div_nonneg (le_of_lt (hρ _)) (le_of_lt (hρ _))) (sq_nonneg _))
    (by
      intro p _
      apply le_of_eq
      field_simp [ne_of_gt (hρ p.1), ne_of_gt (hρ p.2)])
  have hsum : (∑ p : ι × ι, (ρ p.2 / ρ p.1) * B p.2 p.1 ^ 2) = frobenius ρ B := by
    simp only [Fintype.sum_prod_type, frobenius]
    exact sum_comm
  rw [hsum] at hc
  simpa only [Fintype.sum_prod_type, frobenius, Matrix.trace, Matrix.diag,
    Matrix.mul_apply] using hc

theorem trace_power_bound [DecidableEq ι] (M : Matrix ι ι ℝ) (u v : ι → ℝ) (K : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hK : 0 ≤ K) (hr : ∀ i, ∑ j, M i j * v j ≤ K * v i)
    (hl : ∀ j, ∑ i, u i * M i j ≤ K * u j) (n : ℕ) (hn : 4 ≤ n) :
    Matrix.trace (M ^ n) ≤
      K ^ (n - 4) * frobenius (fun i => u i / v i) (M ^ 2) := by
  let ρ : ι → ℝ := fun i => u i / v i
  have hρ : ∀ i, 0 < ρ i := fun i => div_pos (hu i) (hv i)
  have hF := frobenius_nonneg ρ hρ (M ^ 2)
  have hp := frobenius_power_contraction M (M ^ 2) u v K hM hu hv hK hr hl (n - 4)
  have hc := trace_product_sq ρ hρ (M ^ 2) (M ^ (n - 4) * M ^ 2)
  have hexp : 2 + ((n - 4) + 2) = n := by omega
  have hprod : M ^ 2 * (M ^ (n - 4) * M ^ 2) = M ^ n := by
    rw [← pow_add, ← pow_add, hexp]
  rw [hprod] at hc
  have hcomm : (K ^ 2) ^ (n - 4) = (K ^ (n - 4)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hs : Matrix.trace (M ^ n) ^ 2 ≤
      (K ^ (n - 4) * frobenius ρ (M ^ 2)) ^ 2 := by
    calc
      _ ≤ frobenius ρ (M ^ 2) * frobenius ρ (M ^ (n - 4) * M ^ 2) := hc
      _ ≤ frobenius ρ (M ^ 2) * ((K ^ 2) ^ (n - 4) * frobenius ρ (M ^ 2)) :=
        mul_le_mul_of_nonneg_left hp hF
      _ = _ := by rw [hcomm]; ring
  exact le_of_sq_le_sq hs (mul_nonneg (pow_nonneg hK _) hF)

#print axioms frobenius_nonneg
#print axioms row_cauchy
#print axioms energy_contraction
#print axioms frobenius_columns
#print axioms frobenius_contraction
#print axioms frobenius_power_contraction
#print axioms trace_product_sq
#print axioms trace_power_bound

end MathAndTheory.Gyires.WeightedTrace
