module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Milne

abbrev Q := Fin 2
abbrev QQ := Q × Q
abbrev CMatrix := Matrix QQ QQ ℂ

/-- Alice's reduced matrix, tracing out Bob. -/
def partialA (M : CMatrix) : Matrix Q Q ℂ := fun i j => ∑ b, M (i,b) (j,b)

/-- Bob's reduced matrix, tracing out Alice. -/
def partialB (M : CMatrix) : Matrix Q Q ℂ := fun i j => ∑ a, M (a,i) (a,j)

/-- Rank-one operator of a possibly unnormalized vector. -/
def pure {n : Type*} (v : n → ℂ) : Matrix n n ℂ := fun i j => v i * star (v j)

/-- A density matrix in the standard positive-semidefinite, trace-one sense. -/
def Density (M : CMatrix) : Prop := M.PosSemidef ∧ Matrix.trace M = 1

/-- Squared Bloch-vector length of a Hermitian two-dimensional matrix.
For a trace-one matrix this is exactly the conventional qubit Bloch length. -/
def blochSq (A : Matrix Q Q ℂ) : ℝ :=
  (A 0 0).re ^ 2 - 2 * (A 0 0).re * (A 1 1).re + (A 1 1).re ^ 2 +
    4 * Complex.normSq (A 0 1)

/-- Steering-center length of a canonical state with Bob marginal I/2. -/
noncomputable def center (M : CMatrix) : ℝ := Real.sqrt (blochSq (partialA M))

/-- Bob-local filter acting on the two-qubit system. -/
def onBob (F : Matrix Q Q ℂ) : CMatrix := fun i j => if i.1 = j.1 then F i.2 j.2 else 0

/-- Normalization of a state vector. -/
def normSq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- A maximally entangled two-qubit vector has both reductions I/2. -/
def MaximallyEntangled (v : QQ → ℂ) : Prop :=
  partialA (pure v) = ((1 / 2 : ℂ) • (1 : Matrix Q Q ℂ)) ∧
  partialB (pure v) = ((1 / 2 : ℂ) • (1 : Matrix Q Q ℂ))

/-- Born overlap with a pure vector, expressed as a real scalar. -/
def overlap (M : CMatrix) (v : QQ → ℂ) : ℝ :=
  (dotProduct (star v) (M *ᵥ v)).re

end Milne
