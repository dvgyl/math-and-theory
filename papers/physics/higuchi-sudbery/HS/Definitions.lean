import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

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

/-- A three-by-three minor, indexed by the deleted row and column. -/
def minor3 {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R)
    (r c : Fin 4) : R :=
  Matrix.det (M.submatrix (Fin.succAbove r) (Fin.succAbove c))

/-- Sum of the third elementary symmetric functions, in cofactor form. -/
def minorSum (z : Fin 16 → ℂ) : ℝ :=
  ∑ cut : Fin 3, ∑ r : Fin 4, ∑ c : Fin 4,
    Complex.normSq (minor3 (flatten cut z) r c)

/-- Sum of the three balanced marginal purities. -/
def puritySum (z : Fin 16 → ℂ) : ℝ :=
  ∑ cut : Fin 3, (Matrix.trace (reduced cut z * reduced cut z)).re

/-- Third characteristic coefficient as a sum of principal minors. -/
def principalE3 (M : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ r : Fin 4, minor3 M r r

end HS
