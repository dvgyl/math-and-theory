import AllProofs
import NilpotentTensor

/-!
# A genuine density matrix for the nilpotent-pencil counterexample

The algebraic pencil certificates in `NilpotentTensor` are attached here
to an actual positive trace-one complex matrix, with its exact two marginal
matrices and three positive eigenvectors. The later convex/concave-roof
claims are proved in writing, not assumed by these matrix statements.
-/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open MilneExpanded
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open MilneContinuation.NilpotentTensor

namespace MilneContinuation.NilpotentState

def coefficientVector (C : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 × Fin 3 → ℂ :=
  fun p => C p.1 p.2

def identityVector : Fin 3 × Fin 3 → ℂ :=
  coefficientVector !![1,0,0;0,1,0;0,0,1]

theorem identityVector_is_identity : identityVector = coefficientVector 1 := by
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [identityVector, coefficientVector, Matrix.one_apply]
def aVector : Fin 3 × Fin 3 → ℂ := coefficientVector shiftA
def bVector : Fin 3 × Fin 3 → ℂ := coefficientVector shiftB

def counterexampleState : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (((7 : ℝ)⁻¹ : ℝ) : ℂ) •
    (outer identityVector + outer aVector + outer bVector)

def counterexampleMarginal : Matrix (Fin 3) (Fin 3) ℂ :=
  !![2/7,0,0;0,3/7,0;0,0,2/7]

theorem counterexampleState_positive : counterexampleState.PosSemidef := by
  apply (((outer_posSemidef identityVector).add
    (outer_posSemidef aVector)).add (outer_posSemidef bVector)).smul
  exact Complex.zero_le_real.mpr (by norm_num)

theorem counterexample_right_marginal :
    partialTraceRight counterexampleState = counterexampleMarginal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, counterexampleState, counterexampleMarginal,
      outer, Matrix.vecMulVec, coefficientVector, identityVector, aVector, bVector,
      shiftA, shiftB, Matrix.one_apply, Fin.sum_univ_succ]

theorem counterexample_left_marginal :
    partialTraceLeft counterexampleState = counterexampleMarginal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceLeft, counterexampleState, counterexampleMarginal,
      outer, Matrix.vecMulVec, coefficientVector, identityVector, aVector, bVector,
      shiftA, shiftB, Matrix.one_apply, Fin.sum_univ_succ]

theorem counterexampleState_trace_one : counterexampleState.trace = 1 := by
  rw [← trace_partialTraceRight, counterexample_right_marginal]
  norm_num [counterexampleMarginal, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem counterexampleState_is_density :
    counterexampleState.PosSemidef ∧ counterexampleState.trace = 1 :=
  ⟨counterexampleState_positive, counterexampleState_trace_one⟩

theorem identityVector_eigenvalue :
    counterexampleState *ᵥ identityVector = (3/7 : ℂ) • identityVector := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [counterexampleState, outer, Matrix.vecMulVec,
      coefficientVector, identityVector, aVector, bVector, shiftA, shiftB,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem aVector_eigenvalue :
    counterexampleState *ᵥ aVector = (2/7 : ℂ) • aVector := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [counterexampleState, outer, Matrix.vecMulVec,
      coefficientVector, identityVector, aVector, bVector, shiftA, shiftB,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem bVector_eigenvalue :
    counterexampleState *ᵥ bVector = (2/7 : ℂ) • bVector := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [counterexampleState, outer, Matrix.vecMulVec,
      coefficientVector, identityVector, aVector, bVector, shiftA, shiftB,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms identityVector_is_identity
#print axioms counterexampleState_positive
#print axioms counterexample_right_marginal
#print axioms counterexample_left_marginal
#print axioms counterexampleState_trace_one
#print axioms counterexampleState_is_density
#print axioms identityVector_eigenvalue
#print axioms aVector_eigenvalue
#print axioms bVector_eigenvalue

end MilneContinuation.NilpotentState
