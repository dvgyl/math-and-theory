import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

set_option autoImplicit false
namespace BinaryFuglede

abbrev V := Fin 9 → ZMod 2

def decode (n : ℕ) : V := fun i => if n.testBit i.val then 1 else 0

def decodeFin (n : Fin 512) : V := decode n.val

lemma decode_xor (a b : ℕ) : decode (a ^^^ b) = decode a + decode b := by
  funext i
  simp only [decode, Pi.add_apply, Nat.testBit_xor]
  cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;> norm_num
  decide

lemma decode_zero : decode 0 = 0 := by
  funext i
  simp [decode]

lemma decodeFin_injective : Function.Injective decodeFin := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 9
  · have hc := congrFun hab ⟨i, hi⟩
    simp only [decodeFin, decode] at hc
    cases ha : a.val.testBit i <;> cases hb : b.val.testBit i <;> simp_all
  · have hia : a.val < 2 ^ i := lt_of_lt_of_le a.isLt (by
      change 2 ^ 9 ≤ 2 ^ i
      exact Nat.pow_le_pow_right (by decide) (by omega))
    have hib : b.val < 2 ^ i := lt_of_lt_of_le b.isLt (by
      change 2 ^ 9 ≤ 2 ^ i
      exact Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow hia, Nat.testBit_lt_two_pow hib]

lemma card_V : Fintype.card V = 512 := by
  simp [V, Fintype.card_fun, ZMod.card]

lemma decodeFin_bijective : Function.Bijective decodeFin := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨decodeFin_injective, by simp [card_V]⟩

lemma add_self (v : V) : v + v = 0 := by
  funext i
  change v i + v i = 0
  exact CharTwo.add_self_eq_zero _

def xorFin (a b : Fin 512) : Fin 512 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 9) a.isLt b.isLt⟩

lemma decodeFin_xor (a b : Fin 512) :
    decodeFin (xorFin a b) = decodeFin a + decodeFin b := decode_xor _ _

end BinaryFuglede
