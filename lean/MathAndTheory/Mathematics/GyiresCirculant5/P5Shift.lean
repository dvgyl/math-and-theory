module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.ScalarPolynomial
public import Mathlib.Tactic.Ring

/-!
# Expansion in a common shift

`P5 (fun i => a + w i) = ∑ₖ shiftCoeffs w k * a ^ k` (`P5_add_constant`), with explicit
coefficients `shiftCoeff0`, …, `shiftCoeff5`. `eval6` evaluates a polynomial of degree five
given by its six coefficients.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MathAndTheory.GyiresCirculant5

def eval6 (p : Fin 6 → ℝ) (a : ℝ) : ℝ :=
  p 0 + a * (p 1 + a * (p 2 + a * (p 3 + a * (p 4 + a * p 5))))

def shiftCoeff0 (w : Fin 5 → ℝ) : ℝ :=
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

def shiftCoeff1 (w : Fin 5 → ℝ) : ℝ :=
  5 * (w 0) ^ 4 +
    5 * (w 0) ^ 3 * (w 1) +
    5 * (w 0) ^ 3 * (w 2) +
    5 * (w 0) ^ 3 * (w 3) +
    5 * (w 0) ^ 3 * (w 4) +
    5 * (w 0) ^ 2 * (w 1) ^ 2 +
    10 * (w 0) ^ 2 * (w 1) * (w 2) +
    10 * (w 0) ^ 2 * (w 1) * (w 3) +
    15 * (w 0) ^ 2 * (w 1) * (w 4) +
    5 * (w 0) ^ 2 * (w 2) ^ 2 +
    15 * (w 0) ^ 2 * (w 2) * (w 3) +
    10 * (w 0) ^ 2 * (w 2) * (w 4) +
    5 * (w 0) ^ 2 * (w 3) ^ 2 +
    10 * (w 0) ^ 2 * (w 3) * (w 4) +
    5 * (w 0) ^ 2 * (w 4) ^ 2 +
    5 * (w 0) * (w 1) ^ 3 +
    15 * (w 0) * (w 1) ^ 2 * (w 2) +
    10 * (w 0) * (w 1) ^ 2 * (w 3) +
    10 * (w 0) * (w 1) ^ 2 * (w 4) +
    10 * (w 0) * (w 1) * (w 2) ^ 2 +
    15 * (w 0) * (w 1) * (w 2) * (w 3) +
    15 * (w 0) * (w 1) * (w 2) * (w 4) +
    15 * (w 0) * (w 1) * (w 3) ^ 2 +
    15 * (w 0) * (w 1) * (w 3) * (w 4) +
    10 * (w 0) * (w 1) * (w 4) ^ 2 +
    5 * (w 0) * (w 2) ^ 3 +
    10 * (w 0) * (w 2) ^ 2 * (w 3) +
    15 * (w 0) * (w 2) ^ 2 * (w 4) +
    10 * (w 0) * (w 2) * (w 3) ^ 2 +
    15 * (w 0) * (w 2) * (w 3) * (w 4) +
    10 * (w 0) * (w 2) * (w 4) ^ 2 +
    5 * (w 0) * (w 3) ^ 3 +
    10 * (w 0) * (w 3) ^ 2 * (w 4) +
    15 * (w 0) * (w 3) * (w 4) ^ 2 +
    5 * (w 0) * (w 4) ^ 3 +
    5 * (w 1) ^ 4 +
    5 * (w 1) ^ 3 * (w 2) +
    5 * (w 1) ^ 3 * (w 3) +
    5 * (w 1) ^ 3 * (w 4) +
    5 * (w 1) ^ 2 * (w 2) ^ 2 +
    10 * (w 1) ^ 2 * (w 2) * (w 3) +
    10 * (w 1) ^ 2 * (w 2) * (w 4) +
    5 * (w 1) ^ 2 * (w 3) ^ 2 +
    15 * (w 1) ^ 2 * (w 3) * (w 4) +
    5 * (w 1) ^ 2 * (w 4) ^ 2 +
    5 * (w 1) * (w 2) ^ 3 +
    15 * (w 1) * (w 2) ^ 2 * (w 3) +
    10 * (w 1) * (w 2) ^ 2 * (w 4) +
    10 * (w 1) * (w 2) * (w 3) ^ 2 +
    15 * (w 1) * (w 2) * (w 3) * (w 4) +
    15 * (w 1) * (w 2) * (w 4) ^ 2 +
    5 * (w 1) * (w 3) ^ 3 +
    10 * (w 1) * (w 3) ^ 2 * (w 4) +
    10 * (w 1) * (w 3) * (w 4) ^ 2 +
    5 * (w 1) * (w 4) ^ 3 +
    5 * (w 2) ^ 4 +
    5 * (w 2) ^ 3 * (w 3) +
    5 * (w 2) ^ 3 * (w 4) +
    5 * (w 2) ^ 2 * (w 3) ^ 2 +
    10 * (w 2) ^ 2 * (w 3) * (w 4) +
    5 * (w 2) ^ 2 * (w 4) ^ 2 +
    5 * (w 2) * (w 3) ^ 3 +
    15 * (w 2) * (w 3) ^ 2 * (w 4) +
    10 * (w 2) * (w 3) * (w 4) ^ 2 +
    5 * (w 2) * (w 4) ^ 3 +
    5 * (w 3) ^ 4 +
    5 * (w 3) ^ 3 * (w 4) +
    5 * (w 3) ^ 2 * (w 4) ^ 2 +
    5 * (w 3) * (w 4) ^ 3 +
    5 * (w 4) ^ 4

def shiftCoeff2 (w : Fin 5 → ℝ) : ℝ :=
  20 * (w 0) ^ 3 +
    30 * (w 0) ^ 2 * (w 1) +
    30 * (w 0) ^ 2 * (w 2) +
    30 * (w 0) ^ 2 * (w 3) +
    30 * (w 0) ^ 2 * (w 4) +
    30 * (w 0) * (w 1) ^ 2 +
    50 * (w 0) * (w 1) * (w 2) +
    50 * (w 0) * (w 1) * (w 3) +
    50 * (w 0) * (w 1) * (w 4) +
    30 * (w 0) * (w 2) ^ 2 +
    50 * (w 0) * (w 2) * (w 3) +
    50 * (w 0) * (w 2) * (w 4) +
    30 * (w 0) * (w 3) ^ 2 +
    50 * (w 0) * (w 3) * (w 4) +
    30 * (w 0) * (w 4) ^ 2 +
    20 * (w 1) ^ 3 +
    30 * (w 1) ^ 2 * (w 2) +
    30 * (w 1) ^ 2 * (w 3) +
    30 * (w 1) ^ 2 * (w 4) +
    30 * (w 1) * (w 2) ^ 2 +
    50 * (w 1) * (w 2) * (w 3) +
    50 * (w 1) * (w 2) * (w 4) +
    30 * (w 1) * (w 3) ^ 2 +
    50 * (w 1) * (w 3) * (w 4) +
    30 * (w 1) * (w 4) ^ 2 +
    20 * (w 2) ^ 3 +
    30 * (w 2) ^ 2 * (w 3) +
    30 * (w 2) ^ 2 * (w 4) +
    30 * (w 2) * (w 3) ^ 2 +
    50 * (w 2) * (w 3) * (w 4) +
    30 * (w 2) * (w 4) ^ 2 +
    20 * (w 3) ^ 3 +
    30 * (w 3) ^ 2 * (w 4) +
    30 * (w 3) * (w 4) ^ 2 +
    20 * (w 4) ^ 3

def shiftCoeff3 (w : Fin 5 → ℝ) : ℝ :=
  60 * (w 0) ^ 2 +
    90 * (w 0) * (w 1) +
    90 * (w 0) * (w 2) +
    90 * (w 0) * (w 3) +
    90 * (w 0) * (w 4) +
    60 * (w 1) ^ 2 +
    90 * (w 1) * (w 2) +
    90 * (w 1) * (w 3) +
    90 * (w 1) * (w 4) +
    60 * (w 2) ^ 2 +
    90 * (w 2) * (w 3) +
    90 * (w 2) * (w 4) +
    60 * (w 3) ^ 2 +
    90 * (w 3) * (w 4) +
    60 * (w 4) ^ 2

def shiftCoeff4 (w : Fin 5 → ℝ) : ℝ :=
  120 * (w 0) +
    120 * (w 1) +
    120 * (w 2) +
    120 * (w 3) +
    120 * (w 4)

def shiftCoeff5 (_w : Fin 5 → ℝ) : ℝ :=
  120

def shiftCoeffs (w : Fin 5 → ℝ) : Fin 6 → ℝ :=
  ![shiftCoeff0 w, shiftCoeff1 w, shiftCoeff2 w, shiftCoeff3 w, shiftCoeff4 w, shiftCoeff5 w]

@[simp] theorem shiftCoeffs_apply_0 (w : Fin 5 → ℝ) :
    shiftCoeffs w 0 = shiftCoeff0 w := by rfl

@[simp] theorem shiftCoeffs_apply_1 (w : Fin 5 → ℝ) :
    shiftCoeffs w 1 = shiftCoeff1 w := by rfl

@[simp] theorem shiftCoeffs_apply_2 (w : Fin 5 → ℝ) :
    shiftCoeffs w 2 = shiftCoeff2 w := by rfl

@[simp] theorem shiftCoeffs_apply_3 (w : Fin 5 → ℝ) :
    shiftCoeffs w 3 = shiftCoeff3 w := by rfl

@[simp] theorem shiftCoeffs_apply_4 (w : Fin 5 → ℝ) :
    shiftCoeffs w 4 = shiftCoeff4 w := by rfl

@[simp] theorem shiftCoeffs_apply_5 (w : Fin 5 → ℝ) :
    shiftCoeffs w 5 = shiftCoeff5 w := by rfl

theorem P5_add_constant (a : ℝ) (w : Fin 5 → ℝ) :
    P5 (fun i => a + w i) = eval6 (shiftCoeffs w) a := by
  dsimp only [P5, eval6, shiftCoeffs, shiftCoeff0, shiftCoeff1, shiftCoeff2,
    shiftCoeff3, shiftCoeff4, shiftCoeff5, Matrix.cons_val]
  ring

end MathAndTheory.GyiresCirculant5
