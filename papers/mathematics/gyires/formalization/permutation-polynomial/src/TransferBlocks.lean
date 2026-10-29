module

public import GramTrace16
public import MathAndTheory.Mathematics.Gyires.PermutationTransfer
public import Mathlib.Data.Matrix.Block

@[expose] public section

namespace MathAndTheory.Gyires.GramTransfer

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationTransfer
open MathAndTheory.Gyires.PermutationMatrixBridge

abbrev BlockIndex := Fin 1 ⊕ (Fin 4 ⊕ (Fin 6 ⊕ (Fin 4 ⊕ Fin 1)))

def blockState : BlockIndex → State
  | .inl _ => ![0, 0, 0, 0]
  | .inr (.inl i) => ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]] i
  | .inr (.inr (.inl i)) =>
      ![![1,1,0,0], ![1,0,1,0], ![0,1,1,0], ![1,0,0,1], ![0,1,0,1], ![0,0,1,1]] i
  | .inr (.inr (.inr (.inl i))) =>
      ![![1,1,1,0], ![1,1,0,1], ![1,0,1,1], ![0,1,1,1]] i
  | .inr (.inr (.inr (.inr _))) => ![1,1,1,1]

theorem blockState_bijective : Function.Bijective blockState := by decide

noncomputable def blockEquiv : BlockIndex ≃ State :=
  Equiv.ofBijective blockState blockState_bijective

def scalarBlock (f : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => f

noncomputable def blockMatrix (d e f : ℝ) : Matrix BlockIndex BlockIndex ℝ :=
  Matrix.fromBlocks (scalarBlock f) 0 0
    (Matrix.fromBlocks (transferOne d e f) 0 0
      (Matrix.fromBlocks (transferTwo d e f) 0 0
        (Matrix.fromBlocks (transferOne d e f).transpose 0 0 (scalarBlock f))))

set_option maxHeartbeats 2000000 in
theorem fullTransfer_blockMatrix (d e f : ℝ) :
    (fullTransfer (fiveWeights d e f)).submatrix blockEquiv blockEquiv =
      blockMatrix d e f := by
  ext x y
  change fullTransfer (fiveWeights d e f) (blockState x) (blockState y) = blockMatrix d e f x y
  simp only [fullTransfer, Fin.sum_univ_succ]
  rcases x with x | x | x | x | x <;> rcases y with y | y | y | y | y <;>
    fin_cases x <;> fin_cases y <;>
    norm_num [blockState, blockMatrix, scalarBlock, Matrix.fromBlocks,
      transferOne, transferTwo, Matrix.transpose_apply, fiveWeights, Transition, bitValue, letter]

theorem scalarBlock_trace_pow (f : ℝ) (n : ℕ) :
    Matrix.trace (scalarBlock f ^ n) = f^n := by
  have h : scalarBlock f = f • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [scalarBlock]
  rw [h, smul_pow, one_pow, Matrix.trace_smul]
  simp

theorem trace_fromBlocks_diagonal {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    Matrix.trace (Matrix.fromBlocks A 0 0 B) = Matrix.trace A + Matrix.trace B := by
  simp [Matrix.trace, Matrix.fromBlocks, Fintype.sum_sum_type]

theorem submatrix_pow_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (M : Matrix β β ℝ) (e : α ≃ β) (n : ℕ) :
    (M.submatrix e e)^n = (M^n).submatrix e e := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, ← pow_succ]

theorem trace_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix β β ℝ) (e : α ≃ β) :
    Matrix.trace (M.submatrix e e) = Matrix.trace M := by
  exact Equiv.sum_comp e (fun i => M i i)

theorem fullTransfer_trace_formula (d e f : ℝ) (n : ℕ) :
    Matrix.trace (fullTransfer (fiveWeights d e f) ^ n) =
      2*f^n + 2*Matrix.trace (transferOne d e f ^ n) +
        Matrix.trace (transferTwo d e f ^ n) := by
  calc
    _ = Matrix.trace ((fullTransfer (fiveWeights d e f) ^ n).submatrix blockEquiv blockEquiv) :=
      (trace_submatrix_equiv _ blockEquiv).symm
    _ = Matrix.trace (((fullTransfer (fiveWeights d e f)).submatrix blockEquiv blockEquiv)^n) := by
      rw [submatrix_pow_equiv]
    _ = Matrix.trace (blockMatrix d e f ^ n) := by rw [fullTransfer_blockMatrix]
    _ = _ := by
      simp only [blockMatrix, Matrix.fromBlocks_diagonal_pow, trace_fromBlocks_diagonal,
        scalarBlock_trace_pow, ← Matrix.transpose_pow, Matrix.trace_transpose]
      ring

theorem gram_permanent_transfer_formula (n : ℕ) (a b c : ℝ) :
    (polynomialMatrix (finRotate (n+1)) a b c *
      (polynomialMatrix (finRotate (n+1)) a b c).transpose).permanent =
      2*(a*c)^(n+1) +
        2*Matrix.trace (transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c) ^ (n+1)) +
        Matrix.trace (transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c) ^ (n+1)) := by
  rw [gram_permanent_eq_fullTransfer, fullTransfer_trace_formula]

end MathAndTheory.Gyires.GramTransfer
