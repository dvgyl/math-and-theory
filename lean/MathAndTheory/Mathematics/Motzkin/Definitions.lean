module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Sharp root log-concavity for alternating Motzkin sums

This module states the problem without importing its solution.
Zhao, INTEGERS 26 (2026), A55, equations (1) and (2), gives the
recurrence and the finite sum used below. Conjecture 1 asks for
log-concavity of the real roots on the tail starting at nine.

The stronger problem asks for strict log-concavity on the tail
starting at five and proves that no earlier tail is log-concave.
The existence clause makes the recurrence condition nonvacuous.
-/

namespace MathAndTheory.Motzkin.Challenge

open scoped BigOperators

/-- The source recurrence, with its initial values and original index. -/
def IsMotzkin (a : ℕ → ℚ) : Prop :=
  a 0 = 1 ∧ a 1 = 1 ∧
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℚ) + 3) * a (n + 1) =
        (2 * (n : ℚ) + 3) * a n + 3 * (n : ℚ) * a (n - 1)

/-- The finite alternating sum in the source definition. -/
def alternatingSum (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - j) * a j

/-- The real nth root of the finite alternating sum. -/
noncomputable def nthRoot (a : ℕ → ℚ) (n : ℕ) : ℝ :=
  (alternatingSum a n : ℝ) ^ (1 / (n : ℝ))

/-- The tail-five theorem, the failed center-five inequality, and optimality. -/
def Problem : Prop :=
  (∃ a : ℕ → ℚ, IsMotzkin a) ∧
    ∀ a : ℕ → ℚ, IsMotzkin a →
      (∀ n : ℕ, 5 ≤ n →
        nthRoot a n * nthRoot a (n + 2) < nthRoot a (n + 1) ^ (2 : ℕ)) ∧
      nthRoot a 5 ^ (2 : ℕ) < nthRoot a 4 * nthRoot a 6 ∧
      ∀ start : ℕ, start ≤ 4 →
        ¬ (∀ n : ℕ, start ≤ n →
          nthRoot a n * nthRoot a (n + 2) ≤ nthRoot a (n + 1) ^ (2 : ℕ))

end MathAndTheory.Motzkin.Challenge
