module

public import PrototypeExpression

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientRecurrence

open Matrix
open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationTransfer

abbrev Polynomial := SparsePolynomial.Polynomial

local infixl:65 " +ₚ " => SparsePolynomial.add
local infixl:65 " -ₚ " => SparsePolynomial.sub
local infixl:70 " *ₚ " => SparsePolynomial.mul
local infixr:80 " ^ₚ " => SparsePolynomial.pow

abbrev C := SparsePolynomial.const

def scalarStep (B D p0 p1 : Polynomial) : Polynomial := B *ₚ p1 -ₚ D *ₚ p0

def oneInitial (D E F : Polynomial) : Fin 4 → Polynomial :=
  ![C 4, E, C 2 *ₚ D *ₚ F +ₚ (E ^ₚ 2),
    C 3 *ₚ D *ₚ E *ₚ F +ₚ (E ^ₚ 3) +ₚ C 3 *ₚ E *ₚ (F ^ₚ 2)]

def twoInitial (D E F : Polynomial) : Fin 6 → Polynomial :=
  ![C 6, D, (D ^ₚ 2) +ₚ C 2 *ₚ (E ^ₚ 2) +ₚ C 2 *ₚ (F ^ₚ 2),
    (D ^ₚ 3) +ₚ C 3 *ₚ D *ₚ (E ^ₚ 2) +ₚ C 3 *ₚ D *ₚ (F ^ₚ 2) +ₚ C 6 *ₚ (E ^ₚ 2) *ₚ F,
    (D ^ₚ 4) +ₚ C 4 *ₚ (D ^ₚ 2) *ₚ (E ^ₚ 2) +ₚ C 4 *ₚ (D ^ₚ 2) *ₚ (F ^ₚ 2) +ₚ
      C 8 *ₚ D *ₚ (E ^ₚ 2) *ₚ F +ₚ C 2 *ₚ (E ^ₚ 4) +ₚ
      C 8 *ₚ (E ^ₚ 2) *ₚ (F ^ₚ 2) +ₚ C 6 *ₚ (F ^ₚ 4),
    (D ^ₚ 5) +ₚ C 5 *ₚ (D ^ₚ 3) *ₚ (E ^ₚ 2) +ₚ C 5 *ₚ (D ^ₚ 3) *ₚ (F ^ₚ 2) +ₚ
      C 10 *ₚ (D ^ₚ 2) *ₚ (E ^ₚ 2) *ₚ F +ₚ C 5 *ₚ D *ₚ (E ^ₚ 4) +ₚ
      C 15 *ₚ D *ₚ (E ^ₚ 2) *ₚ (F ^ₚ 2) +ₚ C 5 *ₚ D *ₚ (F ^ₚ 4) +ₚ
      C 10 *ₚ (E ^ₚ 4) *ₚ F +ₚ C 10 *ₚ (E ^ₚ 2) *ₚ (F ^ₚ 3)]

def oneStep (D E F : Polynomial) (p : Fin 4 → Polynomial) : Polynomial :=
  E *ₚ p 3 +ₚ (D *ₚ F) *ₚ p 2 +ₚ (E *ₚ (F ^ₚ 2)) *ₚ p 1 +ₚ (F ^ₚ 4) *ₚ p 0

def twoStep (D E F : Polynomial) (p : Fin 6 → Polynomial) : Polynomial :=
  D *ₚ p 5 +ₚ ((E ^ₚ 2) +ₚ (F ^ₚ 2)) *ₚ p 4 +ₚ
    (C 2 *ₚ (E ^ₚ 2) *ₚ F) *ₚ p 3 +ₚ
    (((E ^ₚ 2) *ₚ (F ^ₚ 2)) +ₚ (F ^ₚ 4)) *ₚ p 2 -ₚ
    (D *ₚ (F ^ₚ 4)) *ₚ p 1 -ₚ (F ^ₚ 6) *ₚ p 0

theorem eval_of_same (f : ℕ →* ℝ) (p q : Polynomial)
    (h : SparsePolynomial.same p q = true) : SparsePolynomial.eval f q = SparsePolynomial.eval f p :=
  congrArg (SparsePolynomial.eval f) (SparsePolynomial.same_sound p q h).symm

theorem eval_scalarStep (f : ℕ →* ℝ) (B D p0 p1 : Polynomial) (n : ℕ)
    (h0 : SparsePolynomial.eval f p0 = powerSum (SparsePolynomial.eval f B) (SparsePolynomial.eval f D) n)
    (h1 : SparsePolynomial.eval f p1 = powerSum (SparsePolynomial.eval f B) (SparsePolynomial.eval f D) (n+1)) :
    SparsePolynomial.eval f (scalarStep B D p0 p1) =
      powerSum (SparsePolynomial.eval f B) (SparsePolynomial.eval f D) (n+2) := by
  simp only [scalarStep, SparsePolynomial.eval_sub, SparsePolynomial.eval_mul, h0, h1, powerSum]

theorem eval_power_step (f : ℕ →* ℝ) (B p : Polynomial) (n : ℕ)
    (h : SparsePolynomial.eval f p = (SparsePolynomial.eval f B)^n) :
    SparsePolynomial.eval f (B *ₚ p) = (SparsePolynomial.eval f B)^(n+1) := by
  rw [SparsePolynomial.eval_mul, h, pow_succ']

theorem eval_oneInitial (f : ℕ →* ℝ) (D E F : Polynomial) (i : Fin 4) :
    SparsePolynomial.eval f (oneInitial D E F i) =
      Matrix.trace (transferOne (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
        (SparsePolynomial.eval f F) ^ i.val) := by
  have ht : Matrix.trace (transferOne (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
      (SparsePolynomial.eval f F)) = SparsePolynomial.eval f E := by
    simpa using one_trace_1 (SparsePolynomial.eval f D) (SparsePolynomial.eval f E) (SparsePolynomial.eval f F)
  fin_cases i <;>
    simp [oneInitial, C, SparsePolynomial.eval_add, SparsePolynomial.eval_mul,
      SparsePolynomial.eval_const, SparsePolynomial.eval_pow, ht, one_trace_2, one_trace_3]

theorem eval_twoInitial (f : ℕ →* ℝ) (D E F : Polynomial) (i : Fin 6) :
    SparsePolynomial.eval f (twoInitial D E F i) =
      Matrix.trace (transferTwo (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
        (SparsePolynomial.eval f F) ^ i.val) := by
  have ht : Matrix.trace (transferTwo (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
      (SparsePolynomial.eval f F)) = SparsePolynomial.eval f D := by
    simpa using two_trace_1 (SparsePolynomial.eval f D) (SparsePolynomial.eval f E) (SparsePolynomial.eval f F)
  fin_cases i <;>
    simp [twoInitial, C, SparsePolynomial.eval_add, SparsePolynomial.eval_mul,
      SparsePolynomial.eval_const, SparsePolynomial.eval_pow, ht, two_trace_2, two_trace_3, two_trace_4, two_trace_5]

theorem eval_oneStep (f : ℕ →* ℝ) (D E F : Polynomial) (p : Fin 4 → Polynomial) (n : ℕ)
    (h : ∀ i, SparsePolynomial.eval f (p i) =
      Matrix.trace (transferOne (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
        (SparsePolynomial.eval f F) ^ (n+i.val))) :
    SparsePolynomial.eval f (oneStep D E F p) =
      Matrix.trace (transferOne (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
        (SparsePolynomial.eval f F) ^ (n+4)) := by
  rw [one_trace_recurrence]
  simp [oneStep, SparsePolynomial.eval_add, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, h]

theorem eval_twoStep (f : ℕ →* ℝ) (D E F : Polynomial) (p : Fin 6 → Polynomial) (n : ℕ)
    (h : ∀ i, SparsePolynomial.eval f (p i) =
      Matrix.trace (transferTwo (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
        (SparsePolynomial.eval f F) ^ (n+i.val))) :
    SparsePolynomial.eval f (twoStep D E F p) =
      Matrix.trace (transferTwo (SparsePolynomial.eval f D) (SparsePolynomial.eval f E)
        (SparsePolynomial.eval f F) ^ (n+6)) := by
  rw [two_trace_recurrence]
  simp [twoStep, C, SparsePolynomial.eval_add, SparsePolynomial.eval_sub,
    SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, SparsePolynomial.eval_const, h]

end MathAndTheory.Gyires.PermutationCoefficientRecurrence
