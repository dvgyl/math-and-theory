module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.P5Shift
public import MathAndTheory.Mathematics.Gyires.CirculantFive.FiniteVectorMap

/-!
# Shift coefficients at the autocorrelation vector

The shift coefficients of `P5` evaluated at a vector of the form `![A, B, C, C, B]`, which is
the shape of every autocorrelation vector (`gram_eq_vector`), written as explicit polynomials
`gramShiftCoeff0`, …, `gramShiftCoeff5` in `A`, `B`, `C`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace MathAndTheory.GyiresCirculant5

def gramShiftCoeff0 (A B C : ℝ) : ℝ :=
  A ^ 5 +
    5 * A ^ 3 * B ^ 2 +
    5 * A ^ 3 * C ^ 2 +
    10 * A ^ 2 * B ^ 2 * C +
    10 * A ^ 2 * B * C ^ 2 +
    5 * A * B ^ 4 +
    10 * A * B ^ 3 * C +
    15 * A * B ^ 2 * C ^ 2 +
    10 * A * B * C ^ 3 +
    5 * A * C ^ 4 +
    2 * B ^ 5 +
    10 * B ^ 4 * C +
    10 * B ^ 3 * C ^ 2 +
    10 * B ^ 2 * C ^ 3 +
    10 * B * C ^ 4 +
    2 * C ^ 5

theorem shiftCoeff0_gramVector (A B C : ℝ) :
    shiftCoeff0 (![A,B,C,C,B]) = gramShiftCoeff0 A B C := by
  unfold shiftCoeff0 gramShiftCoeff0
  dsimp only [Matrix.cons_val]
  ring

def gramShiftCoeff1 (A B C : ℝ) : ℝ :=
  5 * A ^ 4 +
    10 * A ^ 3 * B +
    10 * A ^ 3 * C +
    25 * A ^ 2 * B ^ 2 +
    40 * A ^ 2 * B * C +
    25 * A ^ 2 * C ^ 2 +
    30 * A * B ^ 3 +
    80 * A * B ^ 2 * C +
    80 * A * B * C ^ 2 +
    30 * A * C ^ 3 +
    25 * B ^ 4 +
    70 * B ^ 3 * C +
    75 * B ^ 2 * C ^ 2 +
    70 * B * C ^ 3 +
    25 * C ^ 4

theorem shiftCoeff1_gramVector (A B C : ℝ) :
    shiftCoeff1 (![A,B,C,C,B]) = gramShiftCoeff1 A B C := by
  unfold shiftCoeff1 gramShiftCoeff1
  dsimp only [Matrix.cons_val]
  ring

def gramShiftCoeff2 (A B C : ℝ) : ℝ :=
  20 * A ^ 3 +
    60 * A ^ 2 * B +
    60 * A ^ 2 * C +
    110 * A * B ^ 2 +
    200 * A * B * C +
    110 * A * C ^ 2 +
    100 * B ^ 3 +
    220 * B ^ 2 * C +
    220 * B * C ^ 2 +
    100 * C ^ 3

theorem shiftCoeff2_gramVector (A B C : ℝ) :
    shiftCoeff2 (![A,B,C,C,B]) = gramShiftCoeff2 A B C := by
  unfold shiftCoeff2 gramShiftCoeff2
  dsimp only [Matrix.cons_val]
  ring

def gramShiftCoeff3 (A B C : ℝ) : ℝ :=
  60 * A ^ 2 +
    180 * A * B +
    180 * A * C +
    210 * B ^ 2 +
    360 * B * C +
    210 * C ^ 2

theorem shiftCoeff3_gramVector (A B C : ℝ) :
    shiftCoeff3 (![A,B,C,C,B]) = gramShiftCoeff3 A B C := by
  unfold shiftCoeff3 gramShiftCoeff3
  dsimp only [Matrix.cons_val]
  ring

def gramShiftCoeff4 (A B C : ℝ) : ℝ :=
  120 * A +
    240 * B +
    240 * C

theorem shiftCoeff4_gramVector (A B C : ℝ) :
    shiftCoeff4 (![A,B,C,C,B]) = gramShiftCoeff4 A B C := by
  unfold shiftCoeff4 gramShiftCoeff4
  dsimp only [Matrix.cons_val]
  ring

def gramShiftCoeff5 (A B C : ℝ) : ℝ :=
  120

theorem shiftCoeff5_gramVector (A B C : ℝ) :
    shiftCoeff5 (![A,B,C,C,B]) = gramShiftCoeff5 A B C := by
  rfl

def gramShiftCoeffs (A B C : ℝ) : Fin 6 → ℝ := ![gramShiftCoeff0 A B C, gramShiftCoeff1 A B C, gramShiftCoeff2 A B C, gramShiftCoeff3 A B C, gramShiftCoeff4 A B C, gramShiftCoeff5 A B C]

theorem shiftCoeffs_gramVector (A B C : ℝ) :
    shiftCoeffs (![A,B,C,C,B]) = gramShiftCoeffs A B C := by
  unfold shiftCoeffs gramShiftCoeffs
  apply vec6_congr
  · exact shiftCoeff0_gramVector A B C
  · exact shiftCoeff1_gramVector A B C
  · exact shiftCoeff2_gramVector A B C
  · exact shiftCoeff3_gramVector A B C
  · exact shiftCoeff4_gramVector A B C
  · exact shiftCoeff5_gramVector A B C

end MathAndTheory.GyiresCirculant5
