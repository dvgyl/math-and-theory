module

public import Std

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace MathAndTheory.Hofstadter

@[expose] def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

/-- The recursive value, packaged together with the bound that makes every
recursive call in the defining iterate strictly smaller than its input. -/
@[expose] def boundedF (k : Nat) (n : Nat) : {a : Nat // a ≤ n} :=
  match n with
  | 0 => ⟨0, Nat.le_refl 0⟩
  | m + 1 =>
    let g : Fin (m + 1) → Fin (m + 1) := fun x =>
      let y := boundedF k x.val
      ⟨y.val, Nat.lt_of_le_of_lt y.property x.isLt⟩
    let z := iter g k ⟨m, Nat.lt_succ_self m⟩
    ⟨m + 1 - z.val, Nat.sub_le _ _⟩
termination_by n
decreasing_by exact x.isLt

@[expose] def F (k n : Nat) : Nat := (boundedF k n).val

end MathAndTheory.Hofstadter

namespace HofstadterChallenge
open MathAndTheory.Hofstadter
theorem result :
    ∀ k : Nat, 4 ≤ k → ∃ n : Nat,
      iter (F (k + 1)) (2 * k + 2) n < iter (F k) (2 * k + 1) n := by
  sorry
end HofstadterChallenge
