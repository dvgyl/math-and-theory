module

public import SparsePolynomial
public import TransferRecurrences
public import ScalarRecurrences
public import TransferBlocks

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficients

open Matrix Equiv
open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationTransfer
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.GramTransfer

abbrev Polynomial := SparsePolynomial.Polynomial

noncomputable def gramThree (d e f : ℝ) : ℝ :=
  2*f^3 + 2*(3*d*e*f + e^3 + 3*e*f^2) +
    (d^3 + 3*d*e^2 + 3*d*f^2 + 6*e^2*f)

noncomputable def gapThree (a b c : ℝ) : ℝ :=
  27*(a^3+b^3+c^3+3*a*b*c)^2 -
    6*gramThree (a^2+b^2+c^2) (b*(a+c)) (a*c)

theorem actual_square_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (polynomialMatrix (finRotate 3) a b c).permanent^2 = (a^3+b^3+c^3+3*a*b*c)^2 := by
  rw [actual_permanent_square 2 ha hb hc]
  norm_num [permanentSquareExpr, powerSum]
  ring

theorem actual_gram_three (a b c : ℝ) :
    (polynomialMatrix (finRotate 3) a b c *
      (polynomialMatrix (finRotate 3) a b c).transpose).permanent =
      gramThree (a^2+b^2+c^2) (b*(a+c)) (a*c) := by
  rw [gram_permanent_transfer_formula 2 a b c, one_trace_3, two_trace_3]
  rfl

theorem gapThree_eq_actual {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    gapThree a b c =
      27*(polynomialMatrix (finRotate 3) a b c).permanent^2 -
      6*(polynomialMatrix (finRotate 3) a b c *
        (polynomialMatrix (finRotate 3) a b c).transpose).permanent := by
  rw [actual_square_three ha hb hc, actual_gram_three]
  rfl

local infixl:65 " +ₚ " => SparsePolynomial.add
local infixl:65 " -ₚ " => SparsePolynomial.sub
local infixl:70 " *ₚ " => SparsePolynomial.mul
local infixr:80 " ^ₚ " => SparsePolynomial.pow

def polyGramThree (D E F : Polynomial) : Polynomial :=
  SparsePolynomial.const 2 *ₚ (F ^ₚ 3) +ₚ
  SparsePolynomial.const 2 *ₚ
    (SparsePolynomial.const 3 *ₚ D *ₚ E *ₚ F +ₚ (E ^ₚ 3) +ₚ
      SparsePolynomial.const 3 *ₚ E *ₚ (F ^ₚ 2)) +ₚ
  ((D ^ₚ 3) +ₚ SparsePolynomial.const 3 *ₚ D *ₚ (E ^ₚ 2) +ₚ
    SparsePolynomial.const 3 *ₚ D *ₚ (F ^ₚ 2) +ₚ SparsePolynomial.const 6 *ₚ (E ^ₚ 2) *ₚ F)

def polyGapThree (A B C : Polynomial) : Polynomial :=
  SparsePolynomial.const 27 *ₚ
    (((A ^ₚ 3) +ₚ (B ^ₚ 3) +ₚ (C ^ₚ 3) +ₚ SparsePolynomial.const 3 *ₚ A *ₚ B *ₚ C) ^ₚ 2) -ₚ
  SparsePolynomial.const 6 *ₚ polyGramThree
    ((A ^ₚ 2) +ₚ (B ^ₚ 2) +ₚ (C ^ₚ 2)) (B *ₚ (A +ₚ C)) (A *ₚ C)

theorem eval_polyGramThree (f : ℕ →* ℝ) (D E F : Polynomial) :
    SparsePolynomial.eval f (polyGramThree D E F) =
      gramThree (SparsePolynomial.eval f D) (SparsePolynomial.eval f E) (SparsePolynomial.eval f F) := by
  simp [polyGramThree, gramThree, SparsePolynomial.eval_add, SparsePolynomial.eval_mul,
    SparsePolynomial.eval_pow, SparsePolynomial.eval_const]

theorem eval_polyGapThree (f : ℕ →* ℝ) (A B C : Polynomial) :
    SparsePolynomial.eval f (polyGapThree A B C) =
      gapThree (SparsePolynomial.eval f A) (SparsePolynomial.eval f B) (SparsePolynomial.eval f C) := by
  simp [polyGapThree, gapThree, SparsePolynomial.eval_sub, SparsePolynomial.eval_add,
    SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, SparsePolynomial.eval_const,
    eval_polyGramThree]

def primes : Fin 3 → ℕ := ![2,3,5]

theorem primes_prime : ∀ i, (primes i).Prime := by decide +kernel

theorem primes_injective : Function.Injective primes := by decide +kernel

def gapVariables (i : Fin 3) : Polynomial := SparsePolynomial.var (primes i)

theorem eval_gapVariables (z : Fin 3 → ℝ) (i : Fin 3) :
    SparsePolynomial.eval (SparsePolynomial.primeEvaluation primes z) (gapVariables i) = z i := by
  rw [gapVariables, SparsePolynomial.eval_var]
  exact SparsePolynomial.primeEvaluation_prime primes primes_prime primes_injective z i

def chamberWeights : Fin 3 → Fin 3 → Polynomial :=
  let X := gapVariables 0
  let Y := gapVariables 1
  let Z := gapVariables 2
  ![![X, X +ₚ Y, (X +ₚ Y) +ₚ Z],
    ![X +ₚ Y, X, (X +ₚ Y) +ₚ Z],
    ![X, (X +ₚ Y) +ₚ Z, X +ₚ Y]]

def chamberValues (z : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![z 0, z 0+z 1, z 0+z 1+z 2],
    ![z 0+z 1, z 0, z 0+z 1+z 2],
    ![z 0, z 0+z 1+z 2, z 0+z 1]]

theorem eval_chamberWeights (z : Fin 3 → ℝ) (k i : Fin 3) :
    SparsePolynomial.eval (SparsePolynomial.primeEvaluation primes z) (chamberWeights k i) =
      chamberValues z k i := by
  fin_cases k <;> fin_cases i <;>
    simp [chamberWeights, chamberValues, SparsePolynomial.eval_add, eval_gapVariables]

theorem chamberValues_nonneg (z : Fin 3 → ℝ) (hz : ∀ i, 0 ≤ z i) (k i : Fin 3) :
    0 ≤ chamberValues z k i := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  fin_cases k <;> fin_cases i <;> norm_num [chamberValues] <;> linarith

def chamberInput (k : Fin 3) : Polynomial :=
  polyGapThree (chamberWeights k 0) (chamberWeights k 1) (chamberWeights k 2)

theorem eval_chamberInput (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (SparsePolynomial.primeEvaluation primes z) (chamberInput k) =
      gapThree (chamberValues z k 0) (chamberValues z k 1) (chamberValues z k 2) := by
  rw [chamberInput, eval_polyGapThree, eval_chamberWeights, eval_chamberWeights, eval_chamberWeights]

end MathAndTheory.Gyires.PermutationCoefficients
