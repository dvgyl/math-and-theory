module

public import PrefixEvaluation

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationCoefficients

local infixl:65 " +ₚ " => SparsePolynomial.add
local infixl:70 " *ₚ " => SparsePolynomial.mul
local infixr:80 " ^ₚ " => SparsePolynomial.pow

noncomputable abbrev evaluator (z : Fin 3 → ℝ) := SparsePolynomial.primeEvaluation primes z


def weightA (k : Fin 3) : Polynomial := chamberWeights k 0
abbrev realA (z : Fin 3 → ℝ) (k : Fin 3) : ℝ := chamberValues z k 0

@[simp] theorem eval_weightA (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (weightA k) = realA z k :=
  eval_chamberWeights z k 0

def weightB (k : Fin 3) : Polynomial := chamberWeights k 1
abbrev realB (z : Fin 3 → ℝ) (k : Fin 3) : ℝ := chamberValues z k 1

@[simp] theorem eval_weightB (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (weightB k) = realB z k :=
  eval_chamberWeights z k 1

def weightC (k : Fin 3) : Polynomial := chamberWeights k 2
abbrev realC (z : Fin 3 → ℝ) (k : Fin 3) : ℝ := chamberValues z k 2

@[simp] theorem eval_weightC (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (weightC k) = realC z k :=
  eval_chamberWeights z k 2

def squareA (k : Fin 3) : Polynomial := weightA k ^ₚ 2

@[simp] theorem eval_squareA (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (squareA k) = (realA z k)^2 := by
  simp [squareA, SparsePolynomial.eval_pow]

def squareC (k : Fin 3) : Polynomial := weightC k ^ₚ 2

@[simp] theorem eval_squareC (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (squareC k) = (realC z k)^2 := by
  simp [squareC, SparsePolynomial.eval_pow]

def gramD (k : Fin 3) : Polynomial := (weightA k ^ₚ 2) +ₚ (weightB k ^ₚ 2) +ₚ (weightC k ^ₚ 2)

@[simp] theorem eval_gramD (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (gramD k) = (realA z k)^2+(realB z k)^2+(realC z k)^2 := by
  simp [gramD, SparsePolynomial.eval_add, SparsePolynomial.eval_pow]

def gramE (k : Fin 3) : Polynomial := weightB k *ₚ (weightA k +ₚ weightC k)

@[simp] theorem eval_gramE (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (gramE k) = realB z k*(realA z k+realC z k) := by
  simp [gramE, SparsePolynomial.eval_add, SparsePolynomial.eval_mul]

def gramF (k : Fin 3) : Polynomial := weightA k *ₚ weightC k

@[simp] theorem eval_gramF (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (gramF k) = realA z k*realC z k := by
  simp [gramF, SparsePolynomial.eval_mul]

def scalarUB (k : Fin 3) : Polynomial := (weightB k ^ₚ 2) +ₚ SparsePolynomial.const 2 *ₚ weightA k *ₚ weightC k

@[simp] theorem eval_scalarUB (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (scalarUB k) = (realB z k)^2+2*realA z k*realC z k := by
  simp [scalarUB, SparsePolynomial.eval_add, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, SparsePolynomial.eval_const]

def scalarUD (k : Fin 3) : Polynomial := (weightA k *ₚ weightC k) ^ₚ 2

@[simp] theorem eval_scalarUD (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (scalarUD k) = (realA z k*realC z k)^2 := by
  simp [scalarUD, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow]

def scalarVB (k : Fin 3) : Polynomial := weightA k *ₚ weightB k

@[simp] theorem eval_scalarVB (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (scalarVB k) = realA z k*realB z k := by
  simp [scalarVB, SparsePolynomial.eval_mul]

def scalarVD (k : Fin 3) : Polynomial := SparsePolynomial.neg ((weightA k ^ₚ 3) *ₚ weightC k)

@[simp] theorem eval_scalarVD (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (scalarVD k) = -((realA z k)^3*realC z k) := by
  simp [scalarVD, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, SparsePolynomial.eval_neg]

def scalarWB (k : Fin 3) : Polynomial := weightC k *ₚ weightB k

@[simp] theorem eval_scalarWB (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (scalarWB k) = realC z k*realB z k := by
  simp [scalarWB, SparsePolynomial.eval_mul]

def scalarWD (k : Fin 3) : Polynomial := SparsePolynomial.neg (weightA k *ₚ (weightC k ^ₚ 3))

@[simp] theorem eval_scalarWD (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (scalarWD k) = -(realA z k*(realC z k)^3) := by
  simp [scalarWD, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, SparsePolynomial.eval_neg]

end MathAndTheory.Gyires.PermutationCoefficientStage
