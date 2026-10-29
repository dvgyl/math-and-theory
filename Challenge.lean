module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The unrestricted four-qubit entropy bound uses every normalized vector in C^16.
The three reduced matrices are the actual balanced marginal Gram matrices.
Entropy uses natural logarithms. Zero eigenvalues contribute zero. -/
@[expose] public section
open scoped BigOperators
set_option autoImplicit false

namespace HS

/-- The three balanced cuts AB|CD, AC|BD and AD|BC, in this order.
The computational-basis state index is 8 A + 4 B + 2 C + D. -/
def flattenIndex : Fin 3 → Fin 4 → Fin 4 → Fin 16 :=
  ![![![0, 1, 2, 3], ![4, 5, 6, 7], ![8, 9, 10, 11], ![12, 13, 14, 15]],
    ![![0, 1, 4, 5], ![2, 3, 6, 7], ![8, 9, 12, 13], ![10, 11, 14, 15]],
    ![![0, 2, 4, 6], ![1, 3, 5, 7], ![8, 10, 12, 14], ![9, 11, 13, 15]]]

/-- Reshape all sixteen amplitudes across a balanced bipartition. -/
def flatten {R : Type*} (cut : Fin 3) (z : Fin 16 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun r c => z (flattenIndex cut r c)

/-- Squared norm of the unnormalized state. -/
def stateNormSq (z : Fin 16 → ℂ) : ℝ := ∑ i, Complex.normSq (z i)

/-- The unnormalized two-qubit reduced density matrix. -/
def reduced (cut : Fin 3) (z : Fin 16 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  flatten cut z * (flatten cut z).conjTranspose


theorem reduced_isHermitian (cut : Fin 3) (z : Fin 16 → ℂ) :
    (reduced cut z).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

noncomputable def cutEigenvalues (cut : Fin 3) (z : Fin 16 → ℂ) : Fin 4 → ℝ :=
  (reduced_isHermitian cut z).eigenvalues

noncomputable def cutEntropy (cut : Fin 3) (z : Fin 16 → ℂ) : ℝ :=
  ∑ i, -(cutEigenvalues cut z i) * Real.log (cutEigenvalues cut z i)

noncomputable def averageEntropy (z : Fin 16 → ℂ) : ℝ :=
  (∑ cut : Fin 3, cutEntropy cut z) / 3

/-- No marginal condition is imposed. Normalization is the only hypothesis. -/
theorem higuchi_sudbery_bound (z : Fin 16 → ℂ) (hn : stateNormSq z = 1) :
    averageEntropy z ≤ Real.log 2 + Real.log 3 / 2 := by
  sorry

/-- The bound is attained by a normalized four-qubit pure state. -/
theorem higuchi_sudbery_maximum :
    IsGreatest (averageEntropy '' {z : Fin 16 → ℂ | stateNormSq z = 1})
      (Real.log 2 + Real.log 3 / 2) := by
  sorry

end HS
