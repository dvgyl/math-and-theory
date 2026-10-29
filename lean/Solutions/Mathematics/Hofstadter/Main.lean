module
public import MathAndTheory.Mathematics.Hofstadter.Family
public section
namespace HofstadterChallenge
open MathAndTheory.Hofstadter
theorem result :
    ∀ k : Nat, 4 ≤ k → ∃ n : Nat,
      iter (F (k + 1)) (2 * k + 2) n < iter (F k) (2 * k + 1) n := by
  exact MathAndTheory.Hofstadter.Family.infinitely_many_parameter_counterexamples
end HofstadterChallenge
#print axioms HofstadterChallenge.result
