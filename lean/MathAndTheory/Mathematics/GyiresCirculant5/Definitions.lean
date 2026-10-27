module

/- See PROVENANCE.md for source attribution and modifications. -/

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Definitions

For a weight vector `w : Fin 5 → ℝ` (indices modulo five):

* `circ w` is the circulant matrix with entries `circ w i j = w (j - i)`;
* `P5 w` is an explicit homogeneous polynomial of degree five with 26 terms;
  `MatrixBridge.permanent_circ` proves that it is the permanent of `circ w`;
* `gram w k = ∑ i, w i * w (i + k)` is the circular autocorrelation of `w`;
* `conv w k = ∑ i, w i * w (k - i)` is the circular self-convolution of `w`.
-/

@[expose] public section

open scoped BigOperators
namespace MathAndTheory.GyiresCirculant5

def circ (w : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => w (j - i)

def P5 (w : Fin 5 → ℝ) : ℝ :=
    (w 0) ^ 5 +
    5 * (w 0) ^ 3 * (w 1) * (w 4) +
    5 * (w 0) ^ 3 * (w 2) * (w 3) +
    5 * (w 0) ^ 2 * (w 1) ^ 2 * (w 3) +
    5 * (w 0) ^ 2 * (w 1) * (w 2) ^ 2 +
    5 * (w 0) ^ 2 * (w 2) * (w 4) ^ 2 +
    5 * (w 0) ^ 2 * (w 3) ^ 2 * (w 4) +
    5 * (w 0) * (w 1) ^ 3 * (w 2) +
    5 * (w 0) * (w 1) ^ 2 * (w 4) ^ 2 +
    15 * (w 0) * (w 1) * (w 2) * (w 3) * (w 4) +
    5 * (w 0) * (w 1) * (w 3) ^ 3 +
    5 * (w 0) * (w 2) ^ 3 * (w 4) +
    5 * (w 0) * (w 2) ^ 2 * (w 3) ^ 2 +
    5 * (w 0) * (w 3) * (w 4) ^ 3 +
    (w 1) ^ 5 +
    5 * (w 1) ^ 3 * (w 3) * (w 4) +
    5 * (w 1) ^ 2 * (w 2) ^ 2 * (w 4) +
    5 * (w 1) ^ 2 * (w 2) * (w 3) ^ 2 +
    5 * (w 1) * (w 2) ^ 3 * (w 3) +
    5 * (w 1) * (w 2) * (w 4) ^ 3 +
    5 * (w 1) * (w 3) ^ 2 * (w 4) ^ 2 +
    (w 2) ^ 5 +
    5 * (w 2) ^ 2 * (w 3) * (w 4) ^ 2 +
    5 * (w 2) * (w 3) ^ 3 * (w 4) +
    (w 3) ^ 5 +
    (w 4) ^ 5

def gram (w : Fin 5 → ℝ) (k : Fin 5) : ℝ :=
  ∑ i : Fin 5, w i * w (i + k)

def conv (w : Fin 5 → ℝ) (k : Fin 5) : ℝ :=
  ∑ i : Fin 5, w i * w (k - i)

end MathAndTheory.GyiresCirculant5
