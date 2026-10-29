module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.ListLift

/-!
# The six chamber polynomials

For each canonical ordering `k`, `basePolyk` describes the weights of the chamber minus the
smallest weight, as linear polynomials in the first gap, and `chamberPolyk c d e` is the list
of outer coefficients of `strongDefect - 484 (b¹⁰ + c¹⁰ + d¹⁰ + e¹⁰)` in that chamber
(`chamberPolyk_eval`), where `a ≤ a + b ≤ ⋯` are the sorted weights.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace MathAndTheory.GyiresCirculant5

def gapPoly (c d e : ℝ) : List ℝ :=
  [c ^ 10 + d ^ 10 + e ^ 10,0,0,0,0,0,0,0,0,0,1]

theorem gapPoly_eval (b c d e : ℝ) :
    polyEval (gapPoly c d e) b = b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10 := by
  norm_num [gapPoly, polyEval]
  ring

def residualOuter (w : Fin 5 → List ℝ) (c d e : ℝ) (j : Fin 11) : List ℝ :=
  if j = 0 then polyAdd (liftedOuter w j) (polyScale (-484) (gapPoly c d e))
  else liftedOuter w j

theorem eval11_sub_first (p : Fin 11 → ℝ) (a K : ℝ) :
    eval11 (fun j => if j = 0 then p j - K else p j) a = eval11 p a - K := by
  unfold eval11
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (2 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (3 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (4 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (5 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (6 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (7 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (8 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (9 : Fin 11) ≠ 0 by decide),
    ite_eq_right (show (10 : Fin 11) ≠ 0 by decide)]
  exact sub_add_eq_add_sub _ _ _

theorem residualOuter_eval (w : Fin 5 → List ℝ) (a b c d e : ℝ) :
    eval11 (fun j => polyEval (residualOuter w c d e j) b) a =
    eval11 (fun j => polyEval (liftedOuter w j) b) a -
      484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) := by
  have h : (fun j => polyEval (residualOuter w c d e j) b) =
      (fun j => if j = 0 then polyEval (liftedOuter w j) b -
        484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10)
        else polyEval (liftedOuter w j) b) := by
    funext j
    by_cases hj : j = 0
    · simp only [residualOuter, hj, ite_eq_left, polyEval_add, polyEval_scale,
        gapPoly_eval, neg_mul, sub_eq_add_neg]
    · simp only [residualOuter, hj, ite_false]
  rw [h, eval11_sub_first]

def basePoly0 (c d e : ℝ) : Fin 5 → List ℝ := ![[0], [0,1], [c,1], [c+d,1], [c+d+e,1]]

theorem basePoly0_eval (b c d e : ℝ) :
    (fun i => polyEval (basePoly0 c d e i) b) = ![0, b, b + c, b + c + d, b + c + d + e] := by
  funext i
  fin_cases i <;> norm_num [basePoly0, polyEval] <;> ring

def chamberPoly0 (c d e : ℝ) : Fin 11 → List ℝ :=
  residualOuter (basePoly0 c d e) c d e

theorem chamberPoly0_eval (a b c d e : ℝ) :
    eval11 (fun j => polyEval (chamberPoly0 c d e j) b) a =
    strongDefect (![a, a + b, a + b + c, a + b + c + d, a + b + c + d + e]) - 484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) := by
  have hv : (fun i : Fin 5 => a + (![0, b, b + c, b + c + d, b + c + d + e]) i) = ![a, a + b, a + b + c, a + b + c + d, a + b + c + d + e] := by
    funext i
    fin_cases i <;> norm_num <;> ring
  unfold chamberPoly0
  rw [residualOuter_eval, liftedOuter_eval]
  simp only [basePoly0_eval]
  rw [← strongDefect_add_constant, hv]

def basePoly1 (c d e : ℝ) : Fin 5 → List ℝ := ![[0], [0,1], [c,1], [c+d+e,1], [c+d,1]]

theorem basePoly1_eval (b c d e : ℝ) :
    (fun i => polyEval (basePoly1 c d e i) b) = ![0, b, b + c, b + c + d + e, b + c + d] := by
  funext i
  fin_cases i <;> norm_num [basePoly1, polyEval] <;> ring

def chamberPoly1 (c d e : ℝ) : Fin 11 → List ℝ :=
  residualOuter (basePoly1 c d e) c d e

theorem chamberPoly1_eval (a b c d e : ℝ) :
    eval11 (fun j => polyEval (chamberPoly1 c d e j) b) a =
    strongDefect (![a, a + b, a + b + c, a + b + c + d + e, a + b + c + d]) - 484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) := by
  have hv : (fun i : Fin 5 => a + (![0, b, b + c, b + c + d + e, b + c + d]) i) = ![a, a + b, a + b + c, a + b + c + d + e, a + b + c + d] := by
    funext i
    fin_cases i <;> norm_num <;> ring
  unfold chamberPoly1
  rw [residualOuter_eval, liftedOuter_eval]
  simp only [basePoly1_eval]
  rw [← strongDefect_add_constant, hv]

def basePoly2 (c d e : ℝ) : Fin 5 → List ℝ := ![[0], [0,1], [c+d,1], [c,1], [c+d+e,1]]

theorem basePoly2_eval (b c d e : ℝ) :
    (fun i => polyEval (basePoly2 c d e i) b) = ![0, b, b + c + d, b + c, b + c + d + e] := by
  funext i
  fin_cases i <;> norm_num [basePoly2, polyEval] <;> ring

def chamberPoly2 (c d e : ℝ) : Fin 11 → List ℝ :=
  residualOuter (basePoly2 c d e) c d e

theorem chamberPoly2_eval (a b c d e : ℝ) :
    eval11 (fun j => polyEval (chamberPoly2 c d e j) b) a =
    strongDefect (![a, a + b, a + b + c + d, a + b + c, a + b + c + d + e]) - 484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) := by
  have hv : (fun i : Fin 5 => a + (![0, b, b + c + d, b + c, b + c + d + e]) i) = ![a, a + b, a + b + c + d, a + b + c, a + b + c + d + e] := by
    funext i
    fin_cases i <;> norm_num <;> ring
  unfold chamberPoly2
  rw [residualOuter_eval, liftedOuter_eval]
  simp only [basePoly2_eval]
  rw [← strongDefect_add_constant, hv]

def basePoly3 (c d e : ℝ) : Fin 5 → List ℝ := ![[0], [0,1], [c+d+e,1], [c,1], [c+d,1]]

theorem basePoly3_eval (b c d e : ℝ) :
    (fun i => polyEval (basePoly3 c d e i) b) = ![0, b, b + c + d + e, b + c, b + c + d] := by
  funext i
  fin_cases i <;> norm_num [basePoly3, polyEval] <;> ring

def chamberPoly3 (c d e : ℝ) : Fin 11 → List ℝ :=
  residualOuter (basePoly3 c d e) c d e

theorem chamberPoly3_eval (a b c d e : ℝ) :
    eval11 (fun j => polyEval (chamberPoly3 c d e j) b) a =
    strongDefect (![a, a + b, a + b + c + d + e, a + b + c, a + b + c + d]) - 484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) := by
  have hv : (fun i : Fin 5 => a + (![0, b, b + c + d + e, b + c, b + c + d]) i) = ![a, a + b, a + b + c + d + e, a + b + c, a + b + c + d] := by
    funext i
    fin_cases i <;> norm_num <;> ring
  unfold chamberPoly3
  rw [residualOuter_eval, liftedOuter_eval]
  simp only [basePoly3_eval]
  rw [← strongDefect_add_constant, hv]

def basePoly4 (c d e : ℝ) : Fin 5 → List ℝ := ![[0], [0,1], [c+d,1], [c+d+e,1], [c,1]]

theorem basePoly4_eval (b c d e : ℝ) :
    (fun i => polyEval (basePoly4 c d e i) b) = ![0, b, b + c + d, b + c + d + e, b + c] := by
  funext i
  fin_cases i <;> norm_num [basePoly4, polyEval] <;> ring

def chamberPoly4 (c d e : ℝ) : Fin 11 → List ℝ :=
  residualOuter (basePoly4 c d e) c d e

theorem chamberPoly4_eval (a b c d e : ℝ) :
    eval11 (fun j => polyEval (chamberPoly4 c d e j) b) a =
    strongDefect (![a, a + b, a + b + c + d, a + b + c + d + e, a + b + c]) - 484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) := by
  have hv : (fun i : Fin 5 => a + (![0, b, b + c + d, b + c + d + e, b + c]) i) = ![a, a + b, a + b + c + d, a + b + c + d + e, a + b + c] := by
    funext i
    fin_cases i <;> norm_num <;> ring
  unfold chamberPoly4
  rw [residualOuter_eval, liftedOuter_eval]
  simp only [basePoly4_eval]
  rw [← strongDefect_add_constant, hv]

def basePoly5 (c d e : ℝ) : Fin 5 → List ℝ := ![[0], [0,1], [c+d+e,1], [c+d,1], [c,1]]

theorem basePoly5_eval (b c d e : ℝ) :
    (fun i => polyEval (basePoly5 c d e i) b) = ![0, b, b + c + d + e, b + c + d, b + c] := by
  funext i
  fin_cases i <;> norm_num [basePoly5, polyEval] <;> ring

def chamberPoly5 (c d e : ℝ) : Fin 11 → List ℝ :=
  residualOuter (basePoly5 c d e) c d e

theorem chamberPoly5_eval (a b c d e : ℝ) :
    eval11 (fun j => polyEval (chamberPoly5 c d e j) b) a =
    strongDefect (![a, a + b, a + b + c + d + e, a + b + c + d, a + b + c]) - 484 * (b ^ 10 + c ^ 10 + d ^ 10 + e ^ 10) := by
  have hv : (fun i : Fin 5 => a + (![0, b, b + c + d + e, b + c + d, b + c]) i) = ![a, a + b, a + b + c + d + e, a + b + c + d, a + b + c] := by
    funext i
    fin_cases i <;> norm_num <;> ring
  unfold chamberPoly5
  rw [residualOuter_eval, liftedOuter_eval]
  simp only [basePoly5_eval]
  rw [← strongDefect_add_constant, hv]

end MathAndTheory.GyiresCirculant5
