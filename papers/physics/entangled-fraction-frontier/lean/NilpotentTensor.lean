import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Actual finite matrices for failure of nilpotent-pencil tensor closure

These are exact complex-matrix identities. The two-dimensional pencil
`a • shiftA + b • shiftB` consists entirely of nilpotent matrices. Every
single-factor support vector `c I + a A + b B` has determinant `c^3`.
The tensor support nevertheless contains `I + A ⊗ B + B ⊗ A`, which is
singular. This is an algebraic certificate for the written flat-roof
counterexample, not a formalization of convex-roof quantum entanglement.
The nilpotent pencil is classical: these matrices are the transpose of
Christensen, arXiv:funct-an/9702017, Example 3.1, which credits Wielandt
and the earlier work of Motzkin and Taussky. The written report applies
this known pencil to the flat-roof tensor counterexample.

No numerical eigensolver or native decision procedure is used.
-/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker

namespace MilneContinuation.NilpotentTensor

def shiftA : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
def shiftB : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 1, 0, 0; 0, -1, 0]
def pencil (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := a • shiftA + b • shiftB

theorem pencil_entries (a b : ℂ) :
    pencil a b = !![0, a, 0; b, 0, a; 0, -b, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pencil, shiftA, shiftB]

theorem pencil_square (a b : ℂ) :
    pencil a b ^ 2 = !![a*b, 0, a^2; 0, 0, 0; -b^2, 0, -a*b] := by
  rw [pencil_entries, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem pencil_cube_zero (a b : ℂ) : pencil a b ^ 3 = 0 := by
  rw [pow_succ, pencil_square, pencil_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem affine_pencil_determinant (a b c : ℂ) :
    Matrix.det (c • (1 : Matrix (Fin 3) (Fin 3) ℂ) + pencil a b) = c ^ 3 := by
  rw [pencil_entries, Matrix.det_fin_three]
  simp
  ring

/-- The pencil has no common nonzero kernel, despite every element being nilpotent. -/
theorem common_kernel_trivial (v : Fin 3 → ℂ)
    (hA : shiftA *ᵥ v = 0) (hB : shiftB *ᵥ v = 0) : v = 0 := by
  have h1 := congrFun hA 0
  have h2 := congrFun hA 1
  have h0 := congrFun hB 1
  simp [shiftA, shiftB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  funext i
  fin_cases i <;> simp_all

def tensorPencil (x y : ℂ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  1 + x • (shiftA ⊗ₖ shiftB) + y • (shiftB ⊗ₖ shiftA)

abbrev BlockIndex := Fin 1 ⊕ (Fin 2 ⊕ (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)))

def blockMap : BlockIndex → Fin 3 × Fin 3
  | Sum.inl _ => (0, 0)
  | Sum.inr (Sum.inl i) => if i = 0 then (0, 1) else (1, 0)
  | Sum.inr (Sum.inr (Sum.inl i)) =>
      if i = 0 then (0, 2) else if i = 1 then (1, 1) else (2, 0)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) =>
      if i = 0 then (1, 2) else (2, 1)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => (2, 2)

def blockEquiv : BlockIndex ≃ Fin 3 × Fin 3 :=
  Equiv.ofBijective blockMap (by decide)

def twoPlus (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,x;y,1]
def threeBlock (x y : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,-x,0;y,1,x;0,-y,1]
def twoMinus (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,-x;-y,1]

def blockPencil (x y : ℂ) : Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0
    (Matrix.fromBlocks (twoPlus x y) 0 0
      (Matrix.fromBlocks (threeBlock x y) 0 0
        (Matrix.fromBlocks (twoMinus x y) 0 0
          (1 : Matrix (Fin 1) (Fin 1) ℂ))))

/-- The 9 by 9 tensor matrix splits into invariant blocks of sizes 1,2,3,2,1. -/
theorem tensor_block_decomposition (x y : ℂ) :
    (tensorPencil x y).submatrix blockEquiv blockEquiv = blockPencil x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorPencil, blockPencil, blockEquiv, blockMap,
      shiftA, shiftB, twoPlus, threeBlock, twoMinus,
      Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      Matrix.fromBlocks]

theorem tensor_determinant (x y : ℂ) :
    Matrix.det (tensorPencil x y) = (x*y-1)^2 * (2*x*y+1) := by
  rw [← Matrix.det_submatrix_equiv_self blockEquiv (tensorPencil x y),
    tensor_block_decomposition]
  simp only [blockPencil, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    one_mul, mul_one]
  rw [Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_fin_two]
  simp [twoPlus, threeBlock, twoMinus]
  ring

/-- A matrix with nonzero identity coefficient in the tensor support is singular. -/
theorem tensor_determinant_zero (x y : ℂ) (hxy : x*y=1) :
    Matrix.det (tensorPencil x y) = 0 := by
  rw [tensor_determinant, hxy]
  norm_num

theorem tensor_one_one_singular : Matrix.det (tensorPencil 1 1) = 0 :=
  tensor_determinant_zero 1 1 (by norm_num)

#print axioms pencil_cube_zero
#print axioms affine_pencil_determinant
#print axioms common_kernel_trivial
#print axioms tensor_block_decomposition
#print axioms tensor_determinant
#print axioms tensor_determinant_zero
#print axioms tensor_one_one_singular

end MilneContinuation.NilpotentTensor
