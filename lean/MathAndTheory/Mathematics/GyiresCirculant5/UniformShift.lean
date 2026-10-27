module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.P5Shift
public import MathAndTheory.Mathematics.GyiresCirculant5.Defects
public import MathAndTheory.Mathematics.GyiresCirculant5.ScalarPolynomial
public import Mathlib.Tactic.Positivity

/-!
# The defect after a common shift

The autocorrelation of `a + w` is `(5 a² + 2 a S) + gram w`, where `S` is the sum of the
weights (`gram_add_constant`). Hence `strongDefect (fun i => a + w i)` is a polynomial of
degree ten in `a`, whose eleven coefficients `outerCoeff` are given by the shift coefficients
of `P5` at `w` and at `gram w` (`strongDefect_add_constant`). `eval11` evaluates it.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators
namespace MathAndTheory.GyiresCirculant5

def sum5 (w : Fin 5 → ℝ) : ℝ := w 0 + w 1 + w 2 + w 3 + w 4

def eval11 (p : Fin 11 → ℝ) (a : ℝ) : ℝ :=
  p 0 + a * (p 1 + a * (p 2 + a * (p 3 + a * (p 4 + a * (p 5 + a * (p 6 + a * (p 7 + a * (p 8 + a * (p 9 + a * (p 10))))))))))

def outerCoeff (p k : Fin 6 → ℝ) (S : ℝ) : Fin 11 → ℝ :=
  ![
    (625 * (p 0) ^ 2) - (24 * (k 0)),
    (1250 * (p 0) * (p 1)) - (48 * S * (k 1)),
    (1250 * (p 0) * (p 2) + 625 * (p 1) ^ 2) - (120 * (k 1) + 96 * S ^ 2 * (k 2)),
    (1250 * (p 0) * (p 3) + 1250 * (p 1) * (p 2)) - (480 * S * (k 2) + 192 * S ^ 3 * (k 3)),
    (1250 * (p 0) * (p 4) + 1250 * (p 1) * (p 3) + 625 * (p 2) ^ 2) - (600 * (k 2) + 1440 * S ^ 2 * (k 3) + 384 * S ^ 4 * (k 4)),
    (1250 * (p 0) * (p 5) + 1250 * (p 1) * (p 4) + 1250 * (p 2) * (p 3)) - (3600 * S * (k 3) + 3840 * S ^ 3 * (k 4) + 768 * S ^ 5 * (k 5)),
    (1250 * (p 1) * (p 5) + 1250 * (p 2) * (p 4) + 625 * (p 3) ^ 2) - (3000 * (k 3) + 14400 * S ^ 2 * (k 4) + 9600 * S ^ 4 * (k 5)),
    (1250 * (p 2) * (p 5) + 1250 * (p 3) * (p 4)) - (24000 * S * (k 4) + 48000 * S ^ 3 * (k 5)),
    (1250 * (p 3) * (p 5) + 625 * (p 4) ^ 2) - (15000 * (k 4) + 120000 * S ^ 2 * (k 5)),
    (1250 * (p 4) * (p 5)) - (150000 * S * (k 5)),
    (625 * (p 5) ^ 2) - (75000 * (k 5))]

@[simp] theorem outerCoeff_apply_0 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 0 = (625 * (p 0) ^ 2) - (24 * (k 0)) := by rfl

@[simp] theorem outerCoeff_apply_1 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 1 = (1250 * (p 0) * (p 1)) - (48 * S * (k 1)) := by rfl

@[simp] theorem outerCoeff_apply_2 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 2 = (1250 * (p 0) * (p 2) + 625 * (p 1) ^ 2) - (120 * (k 1) + 96 * S ^ 2 * (k 2)) := by rfl

@[simp] theorem outerCoeff_apply_3 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 3 = (1250 * (p 0) * (p 3) + 1250 * (p 1) * (p 2)) - (480 * S * (k 2) + 192 * S ^ 3 * (k 3)) := by rfl

@[simp] theorem outerCoeff_apply_4 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 4 = (1250 * (p 0) * (p 4) + 1250 * (p 1) * (p 3) + 625 * (p 2) ^ 2) - (600 * (k 2) + 1440 * S ^ 2 * (k 3) + 384 * S ^ 4 * (k 4)) := by rfl

@[simp] theorem outerCoeff_apply_5 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 5 = (1250 * (p 0) * (p 5) + 1250 * (p 1) * (p 4) + 1250 * (p 2) * (p 3)) - (3600 * S * (k 3) + 3840 * S ^ 3 * (k 4) + 768 * S ^ 5 * (k 5)) := by rfl

@[simp] theorem outerCoeff_apply_6 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 6 = (1250 * (p 1) * (p 5) + 1250 * (p 2) * (p 4) + 625 * (p 3) ^ 2) - (3000 * (k 3) + 14400 * S ^ 2 * (k 4) + 9600 * S ^ 4 * (k 5)) := by rfl

@[simp] theorem outerCoeff_apply_7 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 7 = (1250 * (p 2) * (p 5) + 1250 * (p 3) * (p 4)) - (24000 * S * (k 4) + 48000 * S ^ 3 * (k 5)) := by rfl

@[simp] theorem outerCoeff_apply_8 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 8 = (1250 * (p 3) * (p 5) + 625 * (p 4) ^ 2) - (15000 * (k 4) + 120000 * S ^ 2 * (k 5)) := by rfl

@[simp] theorem outerCoeff_apply_9 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 9 = (1250 * (p 4) * (p 5)) - (150000 * S * (k 5)) := by rfl

@[simp] theorem outerCoeff_apply_10 (p k : Fin 6 → ℝ) (S : ℝ) :
    outerCoeff p k S 10 = (625 * (p 5) ^ 2) - (75000 * (k 5)) := by rfl

theorem outer_collect (p k : Fin 6 → ℝ) (S a : ℝ) :
    625 * (eval6 p a) ^ 2 - 24 * eval6 k (5 * a ^ 2 + 2 * a * S) =
    eval11 (outerCoeff p k S) a := by
  unfold eval6 eval11 outerCoeff
  dsimp only [Matrix.cons_val]
  ring

theorem gram_add_constant (a : ℝ) (w : Fin 5 → ℝ) :
    gram (fun i => a + w i) =
      fun k => (5 * a ^ 2 + 2 * a * sum5 w) + gram w k := by
  funext k
  fin_cases k <;> norm_num [gram, sum5, Fin.sum_univ_succ]
  · change (a + w 0) * (a + w 0) + ((a + w 1) * (a + w 1) + ((a + w 2) * (a + w 2) + ((a + w 3) * (a + w 3) + ((a + w 4) * (a + w 4))))) =
      (5 * a ^ 2 + 2 * a * (w 0 + w 1 + w 2 + w 3 + w 4)) + (w 0 * w 0 + (w 1 * w 1 + (w 2 * w 2 + (w 3 * w 3 + (w 4 * w 4)))))
    ring
  · change (a + w 0) * (a + w 1) + ((a + w 1) * (a + w 2) + ((a + w 2) * (a + w 3) + ((a + w 3) * (a + w 4) + ((a + w 4) * (a + w 0))))) =
      (5 * a ^ 2 + 2 * a * (w 0 + w 1 + w 2 + w 3 + w 4)) + (w 0 * w 1 + (w 1 * w 2 + (w 2 * w 3 + (w 3 * w 4 + (w 4 * w 0)))))
    ring
  · change (a + w 0) * (a + w 2) + ((a + w 1) * (a + w 3) + ((a + w 2) * (a + w 4) + ((a + w 3) * (a + w 0) + ((a + w 4) * (a + w 1))))) =
      (5 * a ^ 2 + 2 * a * (w 0 + w 1 + w 2 + w 3 + w 4)) + (w 0 * w 2 + (w 1 * w 3 + (w 2 * w 4 + (w 3 * w 0 + (w 4 * w 1)))))
    ring
  · change (a + w 0) * (a + w 3) + ((a + w 1) * (a + w 4) + ((a + w 2) * (a + w 0) + ((a + w 3) * (a + w 1) + ((a + w 4) * (a + w 2))))) =
      (5 * a ^ 2 + 2 * a * (w 0 + w 1 + w 2 + w 3 + w 4)) + (w 0 * w 3 + (w 1 * w 4 + (w 2 * w 0 + (w 3 * w 1 + (w 4 * w 2)))))
    ring
  · change (a + w 0) * (a + w 4) + ((a + w 1) * (a + w 0) + ((a + w 2) * (a + w 1) + ((a + w 3) * (a + w 2) + ((a + w 4) * (a + w 3))))) =
      (5 * a ^ 2 + 2 * a * (w 0 + w 1 + w 2 + w 3 + w 4)) + (w 0 * w 4 + (w 1 * w 0 + (w 2 * w 1 + (w 3 * w 2 + (w 4 * w 3)))))
    ring

theorem strongDefect_add_constant (a : ℝ) (w : Fin 5 → ℝ) :
    strongDefect (fun i => a + w i) =
    eval11 (outerCoeff (shiftCoeffs w) (shiftCoeffs (gram w)) (sum5 w)) a := by
  unfold strongDefect
  rw [P5_add_constant, gram_add_constant, P5_add_constant]
  exact outer_collect _ _ _ _

theorem eval11_nonneg (p : Fin 11 → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hp : ∀ j, 0 ≤ p j) : 0 ≤ eval11 p a := by
  have h0 : 0 ≤ p 0 := hp 0
  have h1 : 0 ≤ p 1 := hp 1
  have h2 : 0 ≤ p 2 := hp 2
  have h3 : 0 ≤ p 3 := hp 3
  have h4 : 0 ≤ p 4 := hp 4
  have h5 : 0 ≤ p 5 := hp 5
  have h6 : 0 ≤ p 6 := hp 6
  have h7 : 0 ≤ p 7 := hp 7
  have h8 : 0 ≤ p 8 := hp 8
  have h9 : 0 ≤ p 9 := hp 9
  have h10 : 0 ≤ p 10 := hp 10
  unfold eval11
  positivity

end MathAndTheory.GyiresCirculant5
