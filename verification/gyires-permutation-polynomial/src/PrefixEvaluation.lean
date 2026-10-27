module

public import PolynomialCoverage

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

abbrev Polynomial := SparsePolynomial.Polynomial

theorem eval_scalar_prefix (f : ℕ →* ℝ) (B D : Polynomial) (data : ℕ → Polynomial) (N : ℕ)
    (h0 : SparsePolynomial.same (SparsePolynomial.const 2) (data 0) = true)
    (h1 : SparsePolynomial.same B (data 1) = true)
    (hs : ∀ n, n+2 ≤ N → SparsePolynomial.same (scalarStep B D (data n) (data (n+1))) (data (n+2)) = true)
    (n : ℕ) (hn : n ≤ N) :
    SparsePolynomial.eval f (data n) = powerSum (SparsePolynomial.eval f B) (SparsePolynomial.eval f D) n := by
  revert hn
  induction n using Nat.twoStepInduction with
  | zero =>
    intro _
    simpa [powerSum, SparsePolynomial.eval_const] using eval_of_same f _ _ h0
  | one =>
    intro _
    simpa [powerSum] using eval_of_same f _ _ h1
  | more n ih0 ih1 =>
    intro hn
    calc
      _ = SparsePolynomial.eval f (scalarStep B D (data n) (data (n+1))) :=
        eval_of_same f _ _ (hs n hn)
      _ = _ := eval_scalarStep f B D (data n) (data (n+1)) n
        (ih0 (by omega)) (ih1 (by omega))

theorem eval_power_prefix (f : ℕ →* ℝ) (B : Polynomial) (data : ℕ → Polynomial) (N : ℕ)
    (h0 : SparsePolynomial.same (SparsePolynomial.const 1) (data 0) = true)
    (hs : ∀ n, n+1 ≤ N → SparsePolynomial.same (SparsePolynomial.mul B (data n)) (data (n+1)) = true)
    (n : ℕ) (hn : n ≤ N) : SparsePolynomial.eval f (data n) = (SparsePolynomial.eval f B)^n := by
  revert hn
  induction n with
  | zero =>
    intro _
    simpa [SparsePolynomial.eval_const] using eval_of_same f _ _ h0
  | succ n ih =>
    intro hn
    calc
      _ = SparsePolynomial.eval f (SparsePolynomial.mul B (data n)) := eval_of_same f _ _ (hs n hn)
      _ = _ := eval_power_step f B (data n) n (ih (by omega))

theorem eval_signed_power (f : ℕ →* ℝ) (p : Polynomial) (n : ℕ) (x : ℝ)
    (h : SparsePolynomial.eval f p = x^n) :
    SparsePolynomial.eval f (SparsePolynomial.mul (SparsePolynomial.const ((-1)^n)) p) = (-x)^n := by
  rw [SparsePolynomial.eval_mul, SparsePolynomial.eval_const, h]
  push_cast
  exact (neg_pow x n).symm

end MathAndTheory.Gyires.PermutationCoefficientStage
