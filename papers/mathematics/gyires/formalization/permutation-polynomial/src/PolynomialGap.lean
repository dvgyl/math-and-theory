module

public import PolynomialRecurrence

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientRecurrence

open Matrix Equiv
open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationTransfer
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.GramTransfer

local infixl:65 " +ₚ " => SparsePolynomial.add
local infixl:65 " -ₚ " => SparsePolynomial.sub
local infixl:70 " *ₚ " => SparsePolynomial.mul

def squareJoin (ap cp u v w fp nfp : Polynomial) : Polynomial :=
  ap +ₚ cp +ₚ u +ₚ C 2 *ₚ v +ₚ C 2 *ₚ w +ₚ C 2 *ₚ fp +ₚ C 2 *ₚ nfp

def gramJoin (fp s1 s2 : Polynomial) : Polynomial := C 2 *ₚ fp +ₚ C 2 *ₚ s1 +ₚ s2

def gapJoin (n : ℕ) (square gram : Polynomial) : Polynomial :=
  C (n^n) *ₚ square -ₚ C n.factorial *ₚ gram

noncomputable def gramExpr (n : ℕ) (a b c : ℝ) : ℝ :=
  2*(a*c)^n + 2*Matrix.trace (transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c)^n) +
    Matrix.trace (transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c)^n)

noncomputable def rawGap (n : ℕ) (a b c : ℝ) : ℝ :=
  (n : ℝ)^n * permanentSquareExpr n a b c - (n.factorial : ℝ)*gramExpr n a b c

theorem eval_squareJoin (f : ℕ →* ℝ) (n : ℕ) (a b c : ℝ)
    (ap cp u v w fp nfp : Polynomial)
    (hap : SparsePolynomial.eval f ap = a^(2*n))
    (hcp : SparsePolynomial.eval f cp = c^(2*n))
    (hu : SparsePolynomial.eval f u = powerSum (b^2+2*a*c) ((a*c)^2) n)
    (hv : SparsePolynomial.eval f v = powerSum (a*b) (-(a^3*c)) n)
    (hw : SparsePolynomial.eval f w = powerSum (c*b) (-(a*c^3)) n)
    (hf : SparsePolynomial.eval f fp = (a*c)^n)
    (hnf : SparsePolynomial.eval f nfp = (-(a*c))^n) :
    SparsePolynomial.eval f (squareJoin ap cp u v w fp nfp) = permanentSquareExpr n a b c := by
  simp [squareJoin, permanentSquareExpr, C, SparsePolynomial.eval_add,
    SparsePolynomial.eval_mul, SparsePolynomial.eval_const, hap, hcp, hu, hv, hw, hf, hnf]

theorem eval_gramJoin (f : ℕ →* ℝ) (n : ℕ) (a b c : ℝ) (fp s1 s2 : Polynomial)
    (hf : SparsePolynomial.eval f fp = (a*c)^n)
    (h1 : SparsePolynomial.eval f s1 =
      Matrix.trace (transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c)^n))
    (h2 : SparsePolynomial.eval f s2 =
      Matrix.trace (transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c)^n)) :
    SparsePolynomial.eval f (gramJoin fp s1 s2) = gramExpr n a b c := by
  simp [gramJoin, gramExpr, C, SparsePolynomial.eval_add, SparsePolynomial.eval_mul,
    SparsePolynomial.eval_const, hf, h1, h2]

theorem eval_gapJoin (f : ℕ →* ℝ) (n : ℕ) (a b c : ℝ) (square gram : Polynomial)
    (hs : SparsePolynomial.eval f square = permanentSquareExpr n a b c)
    (hg : SparsePolynomial.eval f gram = gramExpr n a b c) :
    SparsePolynomial.eval f (gapJoin n square gram) = rawGap n a b c := by
  simp [gapJoin, rawGap, C, SparsePolynomial.eval_sub, SparsePolynomial.eval_mul,
    SparsePolynomial.eval_const, hs, hg]

theorem rawGap_eq_actual (n : ℕ) (hn : 0 < n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    rawGap n a b c =
      (n : ℝ)^n * (polynomialMatrix (finRotate n) a b c).permanent^2 -
      (n.factorial : ℝ) * (polynomialMatrix (finRotate n) a b c *
        (polynomialMatrix (finRotate n) a b c).transpose).permanent := by
  cases n with
  | zero => omega
  | succ n =>
    rw [actual_permanent_square n ha hb hc, gram_permanent_transfer_formula n a b c]
    rfl

theorem both_gram_of_rawGap_nonneg (n : ℕ) (hn : 0 < n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hgap : 0 ≤ rawGap n a b c) :
    let A := polynomialMatrix (finRotate n) a b c
    dimensionConstant n * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant n * (A.transpose*A).permanent ≤ A.permanent^2 := by
  rw [rawGap_eq_actual n hn ha hb hc] at hgap
  have hden : 0 < (n : ℝ)^n := pow_pos (by exact_mod_cast hn) n
  have hleft : dimensionConstant n *
      (polynomialMatrix (finRotate n) a b c * (polynomialMatrix (finRotate n) a b c).transpose).permanent ≤
      (polynomialMatrix (finRotate n) a b c).permanent^2 := by
    unfold dimensionConstant
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  refine ⟨hleft, ?_⟩
  rw [← polynomialMatrix_normal]
  exact hleft

end MathAndTheory.Gyires.PermutationCoefficientRecurrence
