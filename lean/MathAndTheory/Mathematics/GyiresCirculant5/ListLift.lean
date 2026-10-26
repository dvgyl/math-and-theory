module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.PolynomialExpression
public import MathAndTheory.Mathematics.GyiresCirculant5.FiniteVectorMap
public import MathAndTheory.Mathematics.GyiresCirculant5.UniformShift
public import MathAndTheory.Mathematics.GyiresCirculant5.GramListLift

/-!
# The outer coefficients as coefficient lists

The eleven coefficients `outerCoeff` of the shifted defect, lifted to coefficient lists in a
second variable (the first gap). `liftedOuter_eval` proves that evaluating the lifted lists
recovers the outer coefficients, so that the defect in a chamber becomes a polynomial in the
smallest weight `a` whose coefficients are explicit polynomials in the first gap `b`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace MathAndTheory.GyiresCirculant5

def polyShiftCoeff0 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyPow (w 0) 5) (polyScale (5) (polyMul (polyMul (polyPow (w 0) 3) (w 1)) (w 4)))) (polyScale (5) (polyMul (polyMul (polyPow (w 0) 3) (w 2)) (w 3)))) (polyScale (5) (polyMul (polyMul (polyPow (w 0) 2) (polyPow (w 1) 2)) (w 3)))) (polyScale (5) (polyMul (polyMul (polyPow (w 0) 2) (w 1)) (polyPow (w 2) 2)))) (polyScale (5) (polyMul (polyMul (polyPow (w 0) 2) (w 2)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (polyMul (polyPow (w 0) 2) (polyPow (w 3) 2)) (w 4)))) (polyScale (5) (polyMul (polyMul (w 0) (polyPow (w 1) 3)) (w 2)))) (polyScale (5) (polyMul (polyMul (w 0) (polyPow (w 1) 2)) (polyPow (w 4) 2)))) (polyScale (15) (polyMul (polyMul (polyMul (polyMul (w 0) (w 1)) (w 2)) (w 3)) (w 4)))) (polyScale (5) (polyMul (polyMul (w 0) (w 1)) (polyPow (w 3) 3)))) (polyScale (5) (polyMul (polyMul (w 0) (polyPow (w 2) 3)) (w 4)))) (polyScale (5) (polyMul (polyMul (w 0) (polyPow (w 2) 2)) (polyPow (w 3) 2)))) (polyScale (5) (polyMul (polyMul (w 0) (w 3)) (polyPow (w 4) 3)))) (polyPow (w 1) 5)) (polyScale (5) (polyMul (polyMul (polyPow (w 1) 3) (w 3)) (w 4)))) (polyScale (5) (polyMul (polyMul (polyPow (w 1) 2) (polyPow (w 2) 2)) (w 4)))) (polyScale (5) (polyMul (polyMul (polyPow (w 1) 2) (w 2)) (polyPow (w 3) 2)))) (polyScale (5) (polyMul (polyMul (w 1) (polyPow (w 2) 3)) (w 3)))) (polyScale (5) (polyMul (polyMul (w 1) (w 2)) (polyPow (w 4) 3)))) (polyScale (5) (polyMul (polyMul (w 1) (polyPow (w 3) 2)) (polyPow (w 4) 2)))) (polyPow (w 2) 5)) (polyScale (5) (polyMul (polyMul (polyPow (w 2) 2) (w 3)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (polyMul (w 2) (polyPow (w 3) 3)) (w 4)))) (polyPow (w 3) 5)) (polyPow (w 4) 5)

theorem polyShiftCoeff0_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyShiftCoeff0 w) x = shiftCoeff0 (fun i => polyEval (w i) x) := by
  simpa only [polyShiftCoeff0, shiftCoeff0, listInterpret, realInterpret, mul_assoc] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.pow (PolyExpr.var 0) 5) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 1)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 2)) (PolyExpr.var 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.var 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 2)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 3) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 3)) (PolyExpr.var 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 2)) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 3) 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 3)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 2)) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 3)) (PolyExpr.pow (PolyExpr.var 4) 3)))) (PolyExpr.pow (PolyExpr.var 1) 5)) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 3) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.pow (PolyExpr.var 2) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 2)) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 3)) (PolyExpr.var 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)) (PolyExpr.pow (PolyExpr.var 4) 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 3) 2)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.pow (PolyExpr.var 2) 5)) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 2) (PolyExpr.var 3)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.pow (PolyExpr.var 3) 3)) (PolyExpr.var 4)))) (PolyExpr.pow (PolyExpr.var 3) 5)) (PolyExpr.pow (PolyExpr.var 4) 5)) (w) x)

def polyShiftCoeff1 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyScale (5) (polyPow (w 0) 4)) (polyScale (5) (polyMul (polyPow (w 0) 3) (w 1)))) (polyScale (5) (polyMul (polyPow (w 0) 3) (w 2)))) (polyScale (5) (polyMul (polyPow (w 0) 3) (w 3)))) (polyScale (5) (polyMul (polyPow (w 0) 3) (w 4)))) (polyScale (5) (polyMul (polyPow (w 0) 2) (polyPow (w 1) 2)))) (polyScale (10) (polyMul (polyMul (polyPow (w 0) 2) (w 1)) (w 2)))) (polyScale (10) (polyMul (polyMul (polyPow (w 0) 2) (w 1)) (w 3)))) (polyScale (15) (polyMul (polyMul (polyPow (w 0) 2) (w 1)) (w 4)))) (polyScale (5) (polyMul (polyPow (w 0) 2) (polyPow (w 2) 2)))) (polyScale (15) (polyMul (polyMul (polyPow (w 0) 2) (w 2)) (w 3)))) (polyScale (10) (polyMul (polyMul (polyPow (w 0) 2) (w 2)) (w 4)))) (polyScale (5) (polyMul (polyPow (w 0) 2) (polyPow (w 3) 2)))) (polyScale (10) (polyMul (polyMul (polyPow (w 0) 2) (w 3)) (w 4)))) (polyScale (5) (polyMul (polyPow (w 0) 2) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 0) (polyPow (w 1) 3)))) (polyScale (15) (polyMul (polyMul (w 0) (polyPow (w 1) 2)) (w 2)))) (polyScale (10) (polyMul (polyMul (w 0) (polyPow (w 1) 2)) (w 3)))) (polyScale (10) (polyMul (polyMul (w 0) (polyPow (w 1) 2)) (w 4)))) (polyScale (10) (polyMul (polyMul (w 0) (w 1)) (polyPow (w 2) 2)))) (polyScale (15) (polyMul (polyMul (polyMul (w 0) (w 1)) (w 2)) (w 3)))) (polyScale (15) (polyMul (polyMul (polyMul (w 0) (w 1)) (w 2)) (w 4)))) (polyScale (15) (polyMul (polyMul (w 0) (w 1)) (polyPow (w 3) 2)))) (polyScale (15) (polyMul (polyMul (polyMul (w 0) (w 1)) (w 3)) (w 4)))) (polyScale (10) (polyMul (polyMul (w 0) (w 1)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 0) (polyPow (w 2) 3)))) (polyScale (10) (polyMul (polyMul (w 0) (polyPow (w 2) 2)) (w 3)))) (polyScale (15) (polyMul (polyMul (w 0) (polyPow (w 2) 2)) (w 4)))) (polyScale (10) (polyMul (polyMul (w 0) (w 2)) (polyPow (w 3) 2)))) (polyScale (15) (polyMul (polyMul (polyMul (w 0) (w 2)) (w 3)) (w 4)))) (polyScale (10) (polyMul (polyMul (w 0) (w 2)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 0) (polyPow (w 3) 3)))) (polyScale (10) (polyMul (polyMul (w 0) (polyPow (w 3) 2)) (w 4)))) (polyScale (15) (polyMul (polyMul (w 0) (w 3)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 0) (polyPow (w 4) 3)))) (polyScale (5) (polyPow (w 1) 4))) (polyScale (5) (polyMul (polyPow (w 1) 3) (w 2)))) (polyScale (5) (polyMul (polyPow (w 1) 3) (w 3)))) (polyScale (5) (polyMul (polyPow (w 1) 3) (w 4)))) (polyScale (5) (polyMul (polyPow (w 1) 2) (polyPow (w 2) 2)))) (polyScale (10) (polyMul (polyMul (polyPow (w 1) 2) (w 2)) (w 3)))) (polyScale (10) (polyMul (polyMul (polyPow (w 1) 2) (w 2)) (w 4)))) (polyScale (5) (polyMul (polyPow (w 1) 2) (polyPow (w 3) 2)))) (polyScale (15) (polyMul (polyMul (polyPow (w 1) 2) (w 3)) (w 4)))) (polyScale (5) (polyMul (polyPow (w 1) 2) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 1) (polyPow (w 2) 3)))) (polyScale (15) (polyMul (polyMul (w 1) (polyPow (w 2) 2)) (w 3)))) (polyScale (10) (polyMul (polyMul (w 1) (polyPow (w 2) 2)) (w 4)))) (polyScale (10) (polyMul (polyMul (w 1) (w 2)) (polyPow (w 3) 2)))) (polyScale (15) (polyMul (polyMul (polyMul (w 1) (w 2)) (w 3)) (w 4)))) (polyScale (15) (polyMul (polyMul (w 1) (w 2)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 1) (polyPow (w 3) 3)))) (polyScale (10) (polyMul (polyMul (w 1) (polyPow (w 3) 2)) (w 4)))) (polyScale (10) (polyMul (polyMul (w 1) (w 3)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 1) (polyPow (w 4) 3)))) (polyScale (5) (polyPow (w 2) 4))) (polyScale (5) (polyMul (polyPow (w 2) 3) (w 3)))) (polyScale (5) (polyMul (polyPow (w 2) 3) (w 4)))) (polyScale (5) (polyMul (polyPow (w 2) 2) (polyPow (w 3) 2)))) (polyScale (10) (polyMul (polyMul (polyPow (w 2) 2) (w 3)) (w 4)))) (polyScale (5) (polyMul (polyPow (w 2) 2) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 2) (polyPow (w 3) 3)))) (polyScale (15) (polyMul (polyMul (w 2) (polyPow (w 3) 2)) (w 4)))) (polyScale (10) (polyMul (polyMul (w 2) (w 3)) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 2) (polyPow (w 4) 3)))) (polyScale (5) (polyPow (w 3) 4))) (polyScale (5) (polyMul (polyPow (w 3) 3) (w 4)))) (polyScale (5) (polyMul (polyPow (w 3) 2) (polyPow (w 4) 2)))) (polyScale (5) (polyMul (w 3) (polyPow (w 4) 3)))) (polyScale (5) (polyPow (w 4) 4))

theorem polyShiftCoeff1_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyShiftCoeff1 w) x = shiftCoeff1 (fun i => polyEval (w i) x) := by
  simpa only [polyShiftCoeff1, shiftCoeff1, listInterpret, realInterpret, mul_assoc] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (5) (PolyExpr.pow (PolyExpr.var 0) 4)) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 1)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 1) 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)) (PolyExpr.var 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)) (PolyExpr.var 3)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 2)) (PolyExpr.var 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 2)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 3)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.var 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.var 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 2)) (PolyExpr.var 3)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 2)) (PolyExpr.var 4)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 2)) (PolyExpr.var 3)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 3) 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 3) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 3)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 4) 3)))) (PolyExpr.scale (5) (PolyExpr.pow (PolyExpr.var 1) 4))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 3) (PolyExpr.var 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 3) (PolyExpr.var 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 3) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 2)) (PolyExpr.var 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 2)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 3)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 2)) (PolyExpr.var 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 3) 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 3) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 3)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 4) 3)))) (PolyExpr.scale (5) (PolyExpr.pow (PolyExpr.var 2) 4))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 3) (PolyExpr.var 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 3) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 2) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 2) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 2) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.pow (PolyExpr.var 3) 3)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.pow (PolyExpr.var 3) 2)) (PolyExpr.var 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 3)) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.pow (PolyExpr.var 4) 3)))) (PolyExpr.scale (5) (PolyExpr.pow (PolyExpr.var 3) 4))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 3) 3) (PolyExpr.var 4)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 3) 2) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.pow (PolyExpr.var 4) 3)))) (PolyExpr.scale (5) (PolyExpr.pow (PolyExpr.var 4) 4))) (w) x)

def polyShiftCoeff2 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyScale (20) (polyPow (w 0) 3)) (polyScale (30) (polyMul (polyPow (w 0) 2) (w 1)))) (polyScale (30) (polyMul (polyPow (w 0) 2) (w 2)))) (polyScale (30) (polyMul (polyPow (w 0) 2) (w 3)))) (polyScale (30) (polyMul (polyPow (w 0) 2) (w 4)))) (polyScale (30) (polyMul (w 0) (polyPow (w 1) 2)))) (polyScale (50) (polyMul (polyMul (w 0) (w 1)) (w 2)))) (polyScale (50) (polyMul (polyMul (w 0) (w 1)) (w 3)))) (polyScale (50) (polyMul (polyMul (w 0) (w 1)) (w 4)))) (polyScale (30) (polyMul (w 0) (polyPow (w 2) 2)))) (polyScale (50) (polyMul (polyMul (w 0) (w 2)) (w 3)))) (polyScale (50) (polyMul (polyMul (w 0) (w 2)) (w 4)))) (polyScale (30) (polyMul (w 0) (polyPow (w 3) 2)))) (polyScale (50) (polyMul (polyMul (w 0) (w 3)) (w 4)))) (polyScale (30) (polyMul (w 0) (polyPow (w 4) 2)))) (polyScale (20) (polyPow (w 1) 3))) (polyScale (30) (polyMul (polyPow (w 1) 2) (w 2)))) (polyScale (30) (polyMul (polyPow (w 1) 2) (w 3)))) (polyScale (30) (polyMul (polyPow (w 1) 2) (w 4)))) (polyScale (30) (polyMul (w 1) (polyPow (w 2) 2)))) (polyScale (50) (polyMul (polyMul (w 1) (w 2)) (w 3)))) (polyScale (50) (polyMul (polyMul (w 1) (w 2)) (w 4)))) (polyScale (30) (polyMul (w 1) (polyPow (w 3) 2)))) (polyScale (50) (polyMul (polyMul (w 1) (w 3)) (w 4)))) (polyScale (30) (polyMul (w 1) (polyPow (w 4) 2)))) (polyScale (20) (polyPow (w 2) 3))) (polyScale (30) (polyMul (polyPow (w 2) 2) (w 3)))) (polyScale (30) (polyMul (polyPow (w 2) 2) (w 4)))) (polyScale (30) (polyMul (w 2) (polyPow (w 3) 2)))) (polyScale (50) (polyMul (polyMul (w 2) (w 3)) (w 4)))) (polyScale (30) (polyMul (w 2) (polyPow (w 4) 2)))) (polyScale (20) (polyPow (w 3) 3))) (polyScale (30) (polyMul (polyPow (w 3) 2) (w 4)))) (polyScale (30) (polyMul (w 3) (polyPow (w 4) 2)))) (polyScale (20) (polyPow (w 4) 3))

theorem polyShiftCoeff2_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyShiftCoeff2 w) x = shiftCoeff2 (fun i => polyEval (w i) x) := by
  simpa only [polyShiftCoeff2, shiftCoeff2, listInterpret, realInterpret, mul_assoc] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (20) (PolyExpr.pow (PolyExpr.var 0) 3)) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 2)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 3)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 2)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 3)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)) (PolyExpr.var 3)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (20) (PolyExpr.pow (PolyExpr.var 1) 3))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 2)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 3)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)) (PolyExpr.var 3)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (20) (PolyExpr.pow (PolyExpr.var 2) 3))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 2) (PolyExpr.var 3)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 2) 2) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.pow (PolyExpr.var 3) 2)))) (PolyExpr.scale (50) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 3)) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (20) (PolyExpr.pow (PolyExpr.var 3) 3))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 3) 2) (PolyExpr.var 4)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.pow (PolyExpr.var 4) 2)))) (PolyExpr.scale (20) (PolyExpr.pow (PolyExpr.var 4) 3))) (w) x)

def polyShiftCoeff3 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyScale (60) (polyPow (w 0) 2)) (polyScale (90) (polyMul (w 0) (w 1)))) (polyScale (90) (polyMul (w 0) (w 2)))) (polyScale (90) (polyMul (w 0) (w 3)))) (polyScale (90) (polyMul (w 0) (w 4)))) (polyScale (60) (polyPow (w 1) 2))) (polyScale (90) (polyMul (w 1) (w 2)))) (polyScale (90) (polyMul (w 1) (w 3)))) (polyScale (90) (polyMul (w 1) (w 4)))) (polyScale (60) (polyPow (w 2) 2))) (polyScale (90) (polyMul (w 2) (w 3)))) (polyScale (90) (polyMul (w 2) (w 4)))) (polyScale (60) (polyPow (w 3) 2))) (polyScale (90) (polyMul (w 3) (w 4)))) (polyScale (60) (polyPow (w 4) 2))

theorem polyShiftCoeff3_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyShiftCoeff3 w) x = shiftCoeff3 (fun i => polyEval (w i) x) := by
  simpa only [polyShiftCoeff3, shiftCoeff3, listInterpret, realInterpret, mul_assoc] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (60) (PolyExpr.pow (PolyExpr.var 0) 2)) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 3)))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 4)))) (PolyExpr.scale (60) (PolyExpr.pow (PolyExpr.var 1) 2))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 3)))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 4)))) (PolyExpr.scale (60) (PolyExpr.pow (PolyExpr.var 2) 2))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 3)))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 4)))) (PolyExpr.scale (60) (PolyExpr.pow (PolyExpr.var 3) 2))) (PolyExpr.scale (90) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.var 4)))) (PolyExpr.scale (60) (PolyExpr.pow (PolyExpr.var 4) 2))) (w) x)

def polyShiftCoeff4 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyScale (120) (w 0)) (polyScale (120) (w 1))) (polyScale (120) (w 2))) (polyScale (120) (w 3))) (polyScale (120) (w 4))

theorem polyShiftCoeff4_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyShiftCoeff4 w) x = shiftCoeff4 (fun i => polyEval (w i) x) := by
  simpa only [polyShiftCoeff4, shiftCoeff4, listInterpret, realInterpret, mul_assoc] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (120) (PolyExpr.var 0)) (PolyExpr.scale (120) (PolyExpr.var 1))) (PolyExpr.scale (120) (PolyExpr.var 2))) (PolyExpr.scale (120) (PolyExpr.var 3))) (PolyExpr.scale (120) (PolyExpr.var 4))) (w) x)

def polyShiftCoeff5 (w : Fin 5 → List ℝ) : List ℝ :=
  [120]

theorem polyShiftCoeff5_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyShiftCoeff5 w) x = shiftCoeff5 (fun i => polyEval (w i) x) := by
  simpa only [polyShiftCoeff5, shiftCoeff5, listInterpret, realInterpret, mul_assoc] using
    (polyEval_listInterpret (n := 5) (PolyExpr.const (120)) (w) x)

def polyShiftCoeffs (w : Fin 5 → List ℝ) : Fin 6 → List ℝ :=
  ![polyShiftCoeff0 w, polyShiftCoeff1 w, polyShiftCoeff2 w, polyShiftCoeff3 w, polyShiftCoeff4 w, polyShiftCoeff5 w]

theorem polyShiftCoeffs_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    (fun j => polyEval (polyShiftCoeffs w j) x) = shiftCoeffs (fun i => polyEval (w i) x) := by
  calc
    (fun j => polyEval (polyShiftCoeffs w j) x) = ![polyEval (polyShiftCoeff0 w) x, polyEval (polyShiftCoeff1 w) x, polyEval (polyShiftCoeff2 w) x, polyEval (polyShiftCoeff3 w) x, polyEval (polyShiftCoeff4 w) x, polyEval (polyShiftCoeff5 w) x] :=
      map_vec6 (fun p => polyEval p x) (polyShiftCoeff0 w) (polyShiftCoeff1 w) (polyShiftCoeff2 w) (polyShiftCoeff3 w) (polyShiftCoeff4 w) (polyShiftCoeff5 w)
    _ = _ := by
      unfold shiftCoeffs
      apply vec6_congr
      · exact polyShiftCoeff0_eval w x
      · exact polyShiftCoeff1_eval w x
      · exact polyShiftCoeff2_eval w x
      · exact polyShiftCoeff3_eval w x
      · exact polyShiftCoeff4_eval w x
      · exact polyShiftCoeff5_eval w x

def polyGramPart0 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyMul (w 0) (w 0)) (polyMul (w 1) (w 1))) (polyMul (w 2) (w 2))) (polyMul (w 3) (w 3))) (polyMul (w 4) (w 4))

theorem polyGramPart0_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyGramPart0 w) x = (((((polyEval (w 0) x) * (polyEval (w 0) x)) + ((polyEval (w 1) x) * (polyEval (w 1) x))) + ((polyEval (w 2) x) * (polyEval (w 2) x))) + ((polyEval (w 3) x) * (polyEval (w 3) x))) + ((polyEval (w 4) x) * (polyEval (w 4) x)) := by
  simpa only [polyGramPart0, listInterpret, realInterpret] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 0)) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 1))) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 2))) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.var 3))) (PolyExpr.mul (PolyExpr.var 4) (PolyExpr.var 4))) (w) x)

def polyGramPart1 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyMul (w 0) (w 1)) (polyMul (w 1) (w 2))) (polyMul (w 2) (w 3))) (polyMul (w 3) (w 4))) (polyMul (w 4) (w 0))

theorem polyGramPart1_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyGramPart1 w) x = (((((polyEval (w 0) x) * (polyEval (w 1) x)) + ((polyEval (w 1) x) * (polyEval (w 2) x))) + ((polyEval (w 2) x) * (polyEval (w 3) x))) + ((polyEval (w 3) x) * (polyEval (w 4) x))) + ((polyEval (w 4) x) * (polyEval (w 0) x)) := by
  simpa only [polyGramPart1, listInterpret, realInterpret] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2))) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 3))) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.var 4))) (PolyExpr.mul (PolyExpr.var 4) (PolyExpr.var 0))) (w) x)

def polyGramPart2 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyMul (w 0) (w 2)) (polyMul (w 1) (w 3))) (polyMul (w 2) (w 4))) (polyMul (w 3) (w 0))) (polyMul (w 4) (w 1))

theorem polyGramPart2_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polyGramPart2 w) x = (((((polyEval (w 0) x) * (polyEval (w 2) x)) + ((polyEval (w 1) x) * (polyEval (w 3) x))) + ((polyEval (w 2) x) * (polyEval (w 4) x))) + ((polyEval (w 3) x) * (polyEval (w 0) x))) + ((polyEval (w 4) x) * (polyEval (w 1) x)) := by
  simpa only [polyGramPart2, listInterpret, realInterpret] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 3))) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 4))) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.var 0))) (PolyExpr.mul (PolyExpr.var 4) (PolyExpr.var 1))) (w) x)

def polyGram (w : Fin 5 → List ℝ) : Fin 5 → List ℝ :=
  ![polyGramPart0 w, polyGramPart1 w, polyGramPart2 w, polyGramPart2 w, polyGramPart1 w]

private theorem evalVector_eq_vector (w : Fin 5 → List ℝ) (x : ℝ) :
    (fun i => polyEval (w i) x) =
      ![polyEval (w 0) x,polyEval (w 1) x,polyEval (w 2) x,polyEval (w 3) x,polyEval (w 4) x] := by
  funext i
  fin_cases i <;> rfl

theorem polyGram_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    (fun i => polyEval (polyGram w i) x) = gram (fun i => polyEval (w i) x) := by
  calc
    (fun i => polyEval (polyGram w i) x) = ![polyEval (polyGramPart0 w) x, polyEval (polyGramPart1 w) x, polyEval (polyGramPart2 w) x, polyEval (polyGramPart2 w) x, polyEval (polyGramPart1 w) x] :=
      map_vec5 (fun p => polyEval p x) (polyGramPart0 w) (polyGramPart1 w) (polyGramPart2 w) (polyGramPart2 w) (polyGramPart1 w)
    _ = _ := by
      rw [evalVector_eq_vector w x, gram_eq_vector]
      apply vec5_congr
      · exact polyGramPart0_eval w x
      · exact polyGramPart1_eval w x
      · exact polyGramPart2_eval w x
      · exact polyGramPart2_eval w x
      · exact polyGramPart1_eval w x

theorem polyGramShiftParts_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    (fun j => polyEval (polyGramShiftCoeffs
      (polyGramPart0 w) (polyGramPart1 w) (polyGramPart2 w) j) x) =
    shiftCoeffs (gram (fun i => polyEval (w i) x)) := by
  rw [polyGramShiftCoeffs_eval]
  apply congrArg shiftCoeffs
  calc
    ![polyEval (polyGramPart0 w) x, polyEval (polyGramPart1 w) x, polyEval (polyGramPart2 w) x, polyEval (polyGramPart2 w) x, polyEval (polyGramPart1 w) x] = (fun i => polyEval (polyGram w i) x) :=
      (map_vec5 (fun p => polyEval p x) (polyGramPart0 w) (polyGramPart1 w) (polyGramPart2 w) (polyGramPart2 w) (polyGramPart1 w)).symm
    _ = _ := polyGram_eval w x

def polySum5 (w : Fin 5 → List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (w 0) (w 1)) (w 2)) (w 3)) (w 4)

theorem polySum5_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    polyEval (polySum5 w) x = sum5 (fun i => polyEval (w i) x) := by
  simpa only [polySum5, sum5, listInterpret, realInterpret] using
    (polyEval_listInterpret (n := 5) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 2)) (PolyExpr.var 3)) (PolyExpr.var 4)) (w) x)

def polyOuterPart0 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyScale (625) (polyPow (p 0) 2)) (polyScale (-1) (polyScale (24) (k 0)))

theorem polyOuterPart0_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart0 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 0 := by
  rw [outerCoeff_apply_0]
  simpa only [polyOuterPart0, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.scale (625) (PolyExpr.pow (PolyExpr.var 0) 2)) (PolyExpr.scale (-1) (PolyExpr.scale (24) (PolyExpr.var 6)))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart1 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyScale (1250) (polyMul (p 0) (p 1))) (polyScale (-1) (polyScale (48) (polyMul (S) (k 1))))

theorem polyOuterPart1_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart1 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 1 := by
  rw [outerCoeff_apply_1]
  simpa only [polyOuterPart1, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1))) (PolyExpr.scale (-1) (PolyExpr.scale (48) (PolyExpr.mul (PolyExpr.var 12) (PolyExpr.var 7))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart2 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyScale (1250) (polyMul (p 0) (p 2))) (polyScale (625) (polyPow (p 1) 2))) (polyScale (-1) (polyAdd (polyScale (120) (k 1)) (polyScale (96) (polyMul (polyPow (S) 2) (k 2)))))

theorem polyOuterPart2_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart2 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 2 := by
  rw [outerCoeff_apply_2]
  simpa only [polyOuterPart2, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2))) (PolyExpr.scale (625) (PolyExpr.pow (PolyExpr.var 1) 2))) (PolyExpr.scale (-1) (PolyExpr.add (PolyExpr.scale (120) (PolyExpr.var 7)) (PolyExpr.scale (96) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 2) (PolyExpr.var 8)))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart3 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyScale (1250) (polyMul (p 0) (p 3))) (polyScale (1250) (polyMul (p 1) (p 2)))) (polyScale (-1) (polyAdd (polyScale (480) (polyMul (S) (k 2))) (polyScale (192) (polyMul (polyPow (S) 3) (k 3)))))

theorem polyOuterPart3_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart3 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 3 := by
  rw [outerCoeff_apply_3]
  simpa only [polyOuterPart3, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 3))) (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)))) (PolyExpr.scale (-1) (PolyExpr.add (PolyExpr.scale (480) (PolyExpr.mul (PolyExpr.var 12) (PolyExpr.var 8))) (PolyExpr.scale (192) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 3) (PolyExpr.var 9)))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart4 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyScale (1250) (polyMul (p 0) (p 4))) (polyScale (1250) (polyMul (p 1) (p 3)))) (polyScale (625) (polyPow (p 2) 2))) (polyScale (-1) (polyAdd (polyAdd (polyScale (600) (k 2)) (polyScale (1440) (polyMul (polyPow (S) 2) (k 3)))) (polyScale (384) (polyMul (polyPow (S) 4) (k 4)))))

theorem polyOuterPart4_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart4 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 4 := by
  rw [outerCoeff_apply_4]
  simpa only [polyOuterPart4, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 4))) (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 3)))) (PolyExpr.scale (625) (PolyExpr.pow (PolyExpr.var 2) 2))) (PolyExpr.scale (-1) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (600) (PolyExpr.var 8)) (PolyExpr.scale (1440) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 2) (PolyExpr.var 9)))) (PolyExpr.scale (384) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 4) (PolyExpr.var 10)))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart5 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyScale (1250) (polyMul (p 0) (p 5))) (polyScale (1250) (polyMul (p 1) (p 4)))) (polyScale (1250) (polyMul (p 2) (p 3)))) (polyScale (-1) (polyAdd (polyAdd (polyScale (3600) (polyMul (S) (k 3))) (polyScale (3840) (polyMul (polyPow (S) 3) (k 4)))) (polyScale (768) (polyMul (polyPow (S) 5) (k 5)))))

theorem polyOuterPart5_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart5 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 5 := by
  rw [outerCoeff_apply_5]
  simpa only [polyOuterPart5, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 5))) (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 4)))) (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 3)))) (PolyExpr.scale (-1) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (3600) (PolyExpr.mul (PolyExpr.var 12) (PolyExpr.var 9))) (PolyExpr.scale (3840) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 3) (PolyExpr.var 10)))) (PolyExpr.scale (768) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 5) (PolyExpr.var 11)))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart6 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyScale (1250) (polyMul (p 1) (p 5))) (polyScale (1250) (polyMul (p 2) (p 4)))) (polyScale (625) (polyPow (p 3) 2))) (polyScale (-1) (polyAdd (polyAdd (polyScale (3000) (k 3)) (polyScale (14400) (polyMul (polyPow (S) 2) (k 4)))) (polyScale (9600) (polyMul (polyPow (S) 4) (k 5)))))

theorem polyOuterPart6_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart6 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 6 := by
  rw [outerCoeff_apply_6]
  simpa only [polyOuterPart6, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 5))) (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 4)))) (PolyExpr.scale (625) (PolyExpr.pow (PolyExpr.var 3) 2))) (PolyExpr.scale (-1) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (3000) (PolyExpr.var 9)) (PolyExpr.scale (14400) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 2) (PolyExpr.var 10)))) (PolyExpr.scale (9600) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 4) (PolyExpr.var 11)))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart7 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyScale (1250) (polyMul (p 2) (p 5))) (polyScale (1250) (polyMul (p 3) (p 4)))) (polyScale (-1) (polyAdd (polyScale (24000) (polyMul (S) (k 4))) (polyScale (48000) (polyMul (polyPow (S) 3) (k 5)))))

theorem polyOuterPart7_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart7 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 7 := by
  rw [outerCoeff_apply_7]
  simpa only [polyOuterPart7, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 2) (PolyExpr.var 5))) (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.var 4)))) (PolyExpr.scale (-1) (PolyExpr.add (PolyExpr.scale (24000) (PolyExpr.mul (PolyExpr.var 12) (PolyExpr.var 10))) (PolyExpr.scale (48000) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 3) (PolyExpr.var 11)))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart8 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyScale (1250) (polyMul (p 3) (p 5))) (polyScale (625) (polyPow (p 4) 2))) (polyScale (-1) (polyAdd (polyScale (15000) (k 4)) (polyScale (120000) (polyMul (polyPow (S) 2) (k 5)))))

theorem polyOuterPart8_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart8 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 8 := by
  rw [outerCoeff_apply_8]
  simpa only [polyOuterPart8, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 3) (PolyExpr.var 5))) (PolyExpr.scale (625) (PolyExpr.pow (PolyExpr.var 4) 2))) (PolyExpr.scale (-1) (PolyExpr.add (PolyExpr.scale (15000) (PolyExpr.var 10)) (PolyExpr.scale (120000) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 12) 2) (PolyExpr.var 11)))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart9 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyScale (1250) (polyMul (p 4) (p 5))) (polyScale (-1) (polyScale (150000) (polyMul (S) (k 5))))

theorem polyOuterPart9_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart9 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 9 := by
  rw [outerCoeff_apply_9]
  simpa only [polyOuterPart9, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.scale (1250) (PolyExpr.mul (PolyExpr.var 4) (PolyExpr.var 5))) (PolyExpr.scale (-1) (PolyExpr.scale (150000) (PolyExpr.mul (PolyExpr.var 12) (PolyExpr.var 11))))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterPart10 (p k : Fin 6 → List ℝ) (S : List ℝ) : List ℝ :=
  polyAdd (polyScale (625) (polyPow (p 5) 2)) (polyScale (-1) (polyScale (75000) (k 5)))

theorem polyOuterPart10_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    polyEval (polyOuterPart10 p k S) x =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) 10 := by
  rw [outerCoeff_apply_10]
  simpa only [polyOuterPart10, sub_eq_add_neg, neg_one_mul, mul_assoc,
    listInterpret, realInterpret, Matrix.cons_val] using
    (polyEval_listInterpret (n := 13) (PolyExpr.add (PolyExpr.scale (625) (PolyExpr.pow (PolyExpr.var 5) 2)) (PolyExpr.scale (-1) (PolyExpr.scale (75000) (PolyExpr.var 11)))) (![p 0, p 1, p 2, p 3, p 4, p 5, k 0, k 1, k 2, k 3, k 4, k 5, S]) x)

def polyOuterCoeff (p k : Fin 6 → List ℝ) (S : List ℝ) : Fin 11 → List ℝ :=
  ![polyOuterPart0 p k S, polyOuterPart1 p k S, polyOuterPart2 p k S, polyOuterPart3 p k S, polyOuterPart4 p k S, polyOuterPart5 p k S, polyOuterPart6 p k S, polyOuterPart7 p k S, polyOuterPart8 p k S, polyOuterPart9 p k S, polyOuterPart10 p k S]

theorem polyOuterCoeff_eval (p k : Fin 6 → List ℝ) (S : List ℝ) (x : ℝ) :
    (fun j => polyEval (polyOuterCoeff p k S j) x) =
    outerCoeff (fun i => polyEval (p i) x) (fun i => polyEval (k i) x) (polyEval S x) := by
  calc
    (fun j => polyEval (polyOuterCoeff p k S j) x) = ![polyEval (polyOuterPart0 p k S) x, polyEval (polyOuterPart1 p k S) x, polyEval (polyOuterPart2 p k S) x, polyEval (polyOuterPart3 p k S) x, polyEval (polyOuterPart4 p k S) x, polyEval (polyOuterPart5 p k S) x, polyEval (polyOuterPart6 p k S) x, polyEval (polyOuterPart7 p k S) x, polyEval (polyOuterPart8 p k S) x, polyEval (polyOuterPart9 p k S) x, polyEval (polyOuterPart10 p k S) x] :=
      map_vec11 (fun p => polyEval p x) (polyOuterPart0 p k S) (polyOuterPart1 p k S) (polyOuterPart2 p k S) (polyOuterPart3 p k S) (polyOuterPart4 p k S) (polyOuterPart5 p k S) (polyOuterPart6 p k S) (polyOuterPart7 p k S) (polyOuterPart8 p k S) (polyOuterPart9 p k S) (polyOuterPart10 p k S)
    _ = _ := by
      unfold outerCoeff
      apply vec11_congr
      · exact polyOuterPart0_eval p k S x
      · exact polyOuterPart1_eval p k S x
      · exact polyOuterPart2_eval p k S x
      · exact polyOuterPart3_eval p k S x
      · exact polyOuterPart4_eval p k S x
      · exact polyOuterPart5_eval p k S x
      · exact polyOuterPart6_eval p k S x
      · exact polyOuterPart7_eval p k S x
      · exact polyOuterPart8_eval p k S x
      · exact polyOuterPart9_eval p k S x
      · exact polyOuterPart10_eval p k S x

def liftedOuter (w : Fin 5 → List ℝ) : Fin 11 → List ℝ :=
  polyOuterCoeff (polyShiftCoeffs w)
    (polyGramShiftCoeffs (polyGramPart0 w) (polyGramPart1 w) (polyGramPart2 w))
    (polySum5 w)

theorem liftedOuter_eval (w : Fin 5 → List ℝ) (x : ℝ) :
    (fun j => polyEval (liftedOuter w j) x) =
    outerCoeff (shiftCoeffs (fun i => polyEval (w i) x))
      (shiftCoeffs (gram (fun i => polyEval (w i) x))) (sum5 (fun i => polyEval (w i) x)) := by
  unfold liftedOuter
  rw [polyOuterCoeff_eval, polyShiftCoeffs_eval, polyGramShiftParts_eval, polySum5_eval]

end MathAndTheory.GyiresCirculant5
