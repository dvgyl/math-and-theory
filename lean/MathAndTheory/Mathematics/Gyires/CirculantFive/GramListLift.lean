module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.PolynomialExpression
public import MathAndTheory.Mathematics.Gyires.CirculantFive.FiniteVectorMap
public import MathAndTheory.Mathematics.Gyires.CirculantFive.GramShiftScalar

/-!
# Shift coefficients of `P5 ∘ gram` as coefficient lists

The coefficients `gramShiftCoeff0`, …, `gramShiftCoeff5` lifted to coefficient lists in a
variable `x`, with the evaluation identities `polyGramShiftCoeffs_eval`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace MathAndTheory.GyiresCirculant5

def polyGramShiftCoeff0 (A B C : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyPow (A) 5) (polyScale (5) (polyMul (polyPow (A) 3) (polyPow (B) 2)))) (polyScale (5) (polyMul (polyPow (A) 3) (polyPow (C) 2)))) (polyScale (10) (polyMul (polyMul (polyPow (A) 2) (polyPow (B) 2)) (C)))) (polyScale (10) (polyMul (polyMul (polyPow (A) 2) (B)) (polyPow (C) 2)))) (polyScale (5) (polyMul (A) (polyPow (B) 4)))) (polyScale (10) (polyMul (polyMul (A) (polyPow (B) 3)) (C)))) (polyScale (15) (polyMul (polyMul (A) (polyPow (B) 2)) (polyPow (C) 2)))) (polyScale (10) (polyMul (polyMul (A) (B)) (polyPow (C) 3)))) (polyScale (5) (polyMul (A) (polyPow (C) 4)))) (polyScale (2) (polyPow (B) 5))) (polyScale (10) (polyMul (polyPow (B) 4) (C)))) (polyScale (10) (polyMul (polyPow (B) 3) (polyPow (C) 2)))) (polyScale (10) (polyMul (polyPow (B) 2) (polyPow (C) 3)))) (polyScale (10) (polyMul (B) (polyPow (C) 4)))) (polyScale (2) (polyPow (C) 5))

theorem polyGramShiftCoeff0_eval (A B C : List ℝ) (x : ℝ) :
    polyEval (polyGramShiftCoeff0 A B C) x =
      gramShiftCoeff0 (polyEval A x) (polyEval B x) (polyEval C x) := by
  simpa only [polyGramShiftCoeff0, gramShiftCoeff0, listInterpret,
    realInterpret, Matrix.cons_val, mul_assoc] using
    (polyEval_listInterpret (n := 3) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.pow (PolyExpr.var 0) 5) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.pow (PolyExpr.var 1) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.var 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 4)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 3)) (PolyExpr.var 2)))) (PolyExpr.scale (15) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 2) 3)))) (PolyExpr.scale (5) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 4)))) (PolyExpr.scale (2) (PolyExpr.pow (PolyExpr.var 1) 5))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 4) (PolyExpr.var 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 3) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.pow (PolyExpr.var 2) 3)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 4)))) (PolyExpr.scale (2) (PolyExpr.pow (PolyExpr.var 2) 5))) (![A,B,C]) x)

def polyGramShiftCoeff1 (A B C : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyScale (5) (polyPow (A) 4)) (polyScale (10) (polyMul (polyPow (A) 3) (B)))) (polyScale (10) (polyMul (polyPow (A) 3) (C)))) (polyScale (25) (polyMul (polyPow (A) 2) (polyPow (B) 2)))) (polyScale (40) (polyMul (polyMul (polyPow (A) 2) (B)) (C)))) (polyScale (25) (polyMul (polyPow (A) 2) (polyPow (C) 2)))) (polyScale (30) (polyMul (A) (polyPow (B) 3)))) (polyScale (80) (polyMul (polyMul (A) (polyPow (B) 2)) (C)))) (polyScale (80) (polyMul (polyMul (A) (B)) (polyPow (C) 2)))) (polyScale (30) (polyMul (A) (polyPow (C) 3)))) (polyScale (25) (polyPow (B) 4))) (polyScale (70) (polyMul (polyPow (B) 3) (C)))) (polyScale (75) (polyMul (polyPow (B) 2) (polyPow (C) 2)))) (polyScale (70) (polyMul (B) (polyPow (C) 3)))) (polyScale (25) (polyPow (C) 4))

theorem polyGramShiftCoeff1_eval (A B C : List ℝ) (x : ℝ) :
    polyEval (polyGramShiftCoeff1 A B C) x =
      gramShiftCoeff1 (polyEval A x) (polyEval B x) (polyEval C x) := by
  simpa only [polyGramShiftCoeff1, gramShiftCoeff1, listInterpret,
    realInterpret, Matrix.cons_val, mul_assoc] using
    (polyEval_listInterpret (n := 3) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (5) (PolyExpr.pow (PolyExpr.var 0) 4)) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 1)))) (PolyExpr.scale (10) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 3) (PolyExpr.var 2)))) (PolyExpr.scale (25) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 1) 2)))) (PolyExpr.scale (40) (PolyExpr.mul (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)) (PolyExpr.var 2)))) (PolyExpr.scale (25) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 3)))) (PolyExpr.scale (80) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)) (PolyExpr.var 2)))) (PolyExpr.scale (80) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (30) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 3)))) (PolyExpr.scale (25) (PolyExpr.pow (PolyExpr.var 1) 4))) (PolyExpr.scale (70) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 3) (PolyExpr.var 2)))) (PolyExpr.scale (75) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (70) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 3)))) (PolyExpr.scale (25) (PolyExpr.pow (PolyExpr.var 2) 4))) (![A,B,C]) x)

def polyGramShiftCoeff2 (A B C : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyScale (20) (polyPow (A) 3)) (polyScale (60) (polyMul (polyPow (A) 2) (B)))) (polyScale (60) (polyMul (polyPow (A) 2) (C)))) (polyScale (110) (polyMul (A) (polyPow (B) 2)))) (polyScale (200) (polyMul (polyMul (A) (B)) (C)))) (polyScale (110) (polyMul (A) (polyPow (C) 2)))) (polyScale (100) (polyPow (B) 3))) (polyScale (220) (polyMul (polyPow (B) 2) (C)))) (polyScale (220) (polyMul (B) (polyPow (C) 2)))) (polyScale (100) (polyPow (C) 3))

theorem polyGramShiftCoeff2_eval (A B C : List ℝ) (x : ℝ) :
    polyEval (polyGramShiftCoeff2 A B C) x =
      gramShiftCoeff2 (polyEval A x) (polyEval B x) (polyEval C x) := by
  simpa only [polyGramShiftCoeff2, gramShiftCoeff2, listInterpret,
    realInterpret, Matrix.cons_val, mul_assoc] using
    (polyEval_listInterpret (n := 3) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (20) (PolyExpr.pow (PolyExpr.var 0) 3)) (PolyExpr.scale (60) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 1)))) (PolyExpr.scale (60) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 0) 2) (PolyExpr.var 2)))) (PolyExpr.scale (110) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 1) 2)))) (PolyExpr.scale (200) (PolyExpr.mul (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)) (PolyExpr.var 2)))) (PolyExpr.scale (110) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (100) (PolyExpr.pow (PolyExpr.var 1) 3))) (PolyExpr.scale (220) (PolyExpr.mul (PolyExpr.pow (PolyExpr.var 1) 2) (PolyExpr.var 2)))) (PolyExpr.scale (220) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.pow (PolyExpr.var 2) 2)))) (PolyExpr.scale (100) (PolyExpr.pow (PolyExpr.var 2) 3))) (![A,B,C]) x)

def polyGramShiftCoeff3 (A B C : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyAdd (polyAdd (polyAdd (polyScale (60) (polyPow (A) 2)) (polyScale (180) (polyMul (A) (B)))) (polyScale (180) (polyMul (A) (C)))) (polyScale (210) (polyPow (B) 2))) (polyScale (360) (polyMul (B) (C)))) (polyScale (210) (polyPow (C) 2))

theorem polyGramShiftCoeff3_eval (A B C : List ℝ) (x : ℝ) :
    polyEval (polyGramShiftCoeff3 A B C) x =
      gramShiftCoeff3 (polyEval A x) (polyEval B x) (polyEval C x) := by
  simpa only [polyGramShiftCoeff3, gramShiftCoeff3, listInterpret,
    realInterpret, Matrix.cons_val, mul_assoc] using
    (polyEval_listInterpret (n := 3) (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.add (PolyExpr.scale (60) (PolyExpr.pow (PolyExpr.var 0) 2)) (PolyExpr.scale (180) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 1)))) (PolyExpr.scale (180) (PolyExpr.mul (PolyExpr.var 0) (PolyExpr.var 2)))) (PolyExpr.scale (210) (PolyExpr.pow (PolyExpr.var 1) 2))) (PolyExpr.scale (360) (PolyExpr.mul (PolyExpr.var 1) (PolyExpr.var 2)))) (PolyExpr.scale (210) (PolyExpr.pow (PolyExpr.var 2) 2))) (![A,B,C]) x)

def polyGramShiftCoeff4 (A B C : List ℝ) : List ℝ :=
  polyAdd (polyAdd (polyScale (120) (A)) (polyScale (240) (B))) (polyScale (240) (C))

theorem polyGramShiftCoeff4_eval (A B C : List ℝ) (x : ℝ) :
    polyEval (polyGramShiftCoeff4 A B C) x =
      gramShiftCoeff4 (polyEval A x) (polyEval B x) (polyEval C x) := by
  simpa only [polyGramShiftCoeff4, gramShiftCoeff4, listInterpret,
    realInterpret, Matrix.cons_val, mul_assoc] using
    (polyEval_listInterpret (n := 3) (PolyExpr.add (PolyExpr.add (PolyExpr.scale (120) (PolyExpr.var 0)) (PolyExpr.scale (240) (PolyExpr.var 1))) (PolyExpr.scale (240) (PolyExpr.var 2))) (![A,B,C]) x)

def polyGramShiftCoeff5 (A B C : List ℝ) : List ℝ :=
  [120]

theorem polyGramShiftCoeff5_eval (A B C : List ℝ) (x : ℝ) :
    polyEval (polyGramShiftCoeff5 A B C) x =
      gramShiftCoeff5 (polyEval A x) (polyEval B x) (polyEval C x) := by
  simpa only [polyGramShiftCoeff5, gramShiftCoeff5, listInterpret,
    realInterpret, Matrix.cons_val, mul_assoc] using
    (polyEval_listInterpret (n := 3) (PolyExpr.const (120)) (![A,B,C]) x)

def polyGramShiftCoeffs (A B C : List ℝ) : Fin 6 → List ℝ := ![polyGramShiftCoeff0 A B C, polyGramShiftCoeff1 A B C, polyGramShiftCoeff2 A B C, polyGramShiftCoeff3 A B C, polyGramShiftCoeff4 A B C, polyGramShiftCoeff5 A B C]

theorem polyGramShiftCoeffs_eval (A B C : List ℝ) (x : ℝ) :
    (fun j => polyEval (polyGramShiftCoeffs A B C j) x) =
    shiftCoeffs (![polyEval A x, polyEval B x, polyEval C x, polyEval C x, polyEval B x]) := by
  calc
    (fun j => polyEval (polyGramShiftCoeffs A B C j) x) = ![polyEval (polyGramShiftCoeff0 A B C) x, polyEval (polyGramShiftCoeff1 A B C) x, polyEval (polyGramShiftCoeff2 A B C) x, polyEval (polyGramShiftCoeff3 A B C) x, polyEval (polyGramShiftCoeff4 A B C) x, polyEval (polyGramShiftCoeff5 A B C) x] :=
      map_vec6 (fun p => polyEval p x) (polyGramShiftCoeff0 A B C) (polyGramShiftCoeff1 A B C) (polyGramShiftCoeff2 A B C) (polyGramShiftCoeff3 A B C) (polyGramShiftCoeff4 A B C) (polyGramShiftCoeff5 A B C)
    _ = gramShiftCoeffs (polyEval A x) (polyEval B x) (polyEval C x) := by
      unfold gramShiftCoeffs
      apply vec6_congr
      · exact polyGramShiftCoeff0_eval A B C x
      · exact polyGramShiftCoeff1_eval A B C x
      · exact polyGramShiftCoeff2_eval A B C x
      · exact polyGramShiftCoeff3_eval A B C x
      · exact polyGramShiftCoeff4_eval A B C x
      · exact polyGramShiftCoeff5_eval A B C x
    _ = _ := (shiftCoeffs_gramVector _ _ _).symm

end MathAndTheory.GyiresCirculant5
