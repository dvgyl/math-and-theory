import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases

/-! A deliberately small import boundary for the closed integer computations.
These formulas are definitionally the same as the mathematical definitions in
IntegerCross and IntegerEmbedding; the aggregate modules reconnect the proofs.
-/

open scoped BigOperators

namespace ADMMNearSharpCertificate.IntArithmetic

def integerCross {κ : Type*} (a b : κ → ℤ) : Matrix κ κ ℤ :=
  fun k l => a k * b l + b k * a l

def weightedDifferences {ν κ : Type*} [Fintype ν]
    (lam : Matrix ν ν ℤ) (X : Matrix ν κ ℤ) : Matrix ν κ ℤ :=
  fun i k => ∑ j, lam i j * (X j k-X i k)

def embeddedEntry {n N : ℕ} (a b : ℕ) (P : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin N) : ℤ :=
  if hi : a ≤ i.val ∧ i.val-a<n then
    if hj : b ≤ j.val ∧ j.val-b<n then
      P ⟨i.val-a,hi.2⟩ ⟨j.val-b,hj.2⟩
    else 0
  else 0

end ADMMNearSharpCertificate.IntArithmetic
