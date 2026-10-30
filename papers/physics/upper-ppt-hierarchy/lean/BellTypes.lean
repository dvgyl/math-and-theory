import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Prod

open scoped BigOperators Matrix

set_option maxHeartbeats 5000000

namespace BellBridge

def BIndex : ℕ → Type
  | 0 => PUnit
  | n + 1 => BIndex n × Fin 4

def QIndex : ℕ → Type
  | 0 => PUnit
  | n + 1 => QIndex n × Fin 2

instance bFintype (n : ℕ) : Fintype (BIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (BIndex n × Fin 4))

instance bDecidableEq (n : ℕ) : DecidableEq (BIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (BIndex n × Fin 4))

instance qFintype (n : ℕ) : Fintype (QIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (QIndex n × Fin 2))

instance qDecidableEq (n : ℕ) : DecidableEq (QIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (QIndex n × Fin 2))

abbrev HIndex (n : ℕ) := QIndex n × QIndex n
abbrev CMatrix (n : ℕ) := Matrix (HIndex n) (HIndex n) ℂ

def bellVec (j : Fin 4) (a b : Fin 2) : ℚ :=
  if j.val < 2 then
    if a = b then if j.val = 0 ∨ a.val = 0 then 1 else -1 else 0
  else
    if a ≠ b then if j.val = 2 ∨ a.val = 0 then 1 else -1 else 0

def vec : (n : ℕ) → BIndex n → HIndex n → ℚ
  | 0, _, _ => 1
  | n+1, (j,k), ((a,α),(e,β)) => vec n j (a,e) * bellVec k α β

def P (n : ℕ) (j : BIndex n) : Matrix (HIndex n) (HIndex n) ℚ :=
  fun a b => vec n j a * vec n j b / (2:ℚ)^n

def singleT (i j : Fin 4) : ℚ := if i.val + j.val = 3 then -(1/2) else 1/2

def T : (n : ℕ) → Matrix (BIndex n) (BIndex n) ℚ
  | 0, _, _ => 1
  | n+1, (i,k), (j,l) => T n i j * singleT k l

def pt {R : Type*} (n : ℕ) (X : Matrix (HIndex n) (HIndex n) R) :
    Matrix (HIndex n) (HIndex n) R :=
  fun a b => X (a.1,b.2) (b.1,a.2)

@[simp] theorem pt_pt {R : Type*} (n : ℕ)
    (X : Matrix (HIndex n) (HIndex n) R) : pt n (pt n X) = X := by
  rfl

theorem T_symmetric (n : ℕ) (i j : BIndex n) : T n i j = T n j i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨i,k⟩
    rcases j with ⟨j,l⟩
    simp only [T, ih i j, singleT, add_comm]

end BellBridge
