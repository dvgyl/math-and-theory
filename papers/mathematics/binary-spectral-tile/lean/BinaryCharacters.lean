import BinaryData
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
open scoped BigOperators
namespace BinaryFuglede

def binaryDot (u x : V) : ZMod 2 := ∑ k, u k * x k

def intCharacter (u x : V) : ℤ := if binaryDot u x = 0 then 1 else -1

def character (u x : V) : ℂ := (intCharacter u x : ℂ)

lemma binaryDot_add (u x y : V) : binaryDot u (x+y) = binaryDot u x + binaryDot u y := by
  simp [binaryDot, mul_add, Finset.sum_add_distrib]

lemma binaryDot_add_left (u v x : V) : binaryDot (u+v) x = binaryDot u x + binaryDot v x := by
  simp [binaryDot, add_mul, Finset.sum_add_distrib]

lemma intCharacter_zero (u : V) : intCharacter u 0 = 1 := by simp [intCharacter,binaryDot]

lemma intCharacter_zero_left (x : V) : intCharacter 0 x = 1 := by simp [intCharacter,binaryDot]

lemma intCharacter_add (u x y : V) : intCharacter u (x+y) = intCharacter u x * intCharacter u y := by
  unfold intCharacter
  rw [binaryDot_add]
  generalize binaryDot u x = a
  generalize binaryDot u y = b
  fin_cases a <;> fin_cases b <;> norm_num
  decide

lemma intCharacter_add_left (u v x : V) : intCharacter (u+v) x = intCharacter u x * intCharacter v x := by
  unfold intCharacter
  rw [binaryDot_add_left]
  generalize binaryDot u x = a
  generalize binaryDot v x = b
  fin_cases a <;> fin_cases b <;> norm_num
  decide

lemma character_add (u x y : V) : character u (x+y) = character u x * character u y := by
  simp [character,intCharacter_add]

lemma character_add_left (u v x : V) : character (u+v) x = character u x * character v x := by
  simp [character,intCharacter_add_left]

lemma character_zero (u : V) : character u 0 = 1 := by simp [character,intCharacter_zero]

lemma character_zero_left (x : V) : character 0 x = 1 := by simp [character,intCharacter_zero_left]

lemma character_conj (u x : V) : star (character u x) = character u x := by
  simp [character]

lemma character_sq (u x : V) : character u x * character u x = 1 := by
  rw [← character_add, add_self, character_zero]

def characterHom (u : V) : AddChar V ℂ where
  toFun := character u
  map_zero_eq_one' := character_zero u
  map_add_eq_mul' := character_add u

private theorem check_one : (∑ j : Fin 64, intCharacter (decode 1) (point j)) = 0 := by decide

end BinaryFuglede
