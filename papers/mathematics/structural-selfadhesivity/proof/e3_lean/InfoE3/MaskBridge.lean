import InfoE3.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace InfoE3

/-- Literal subsets of the n-element ground set, read from incidence bits. -/
def decodeMask {n : Nat} (m : Mask n) : Finset (Fin n) :=
  Finset.univ.filter fun i => m.val.testBit i.val

/-- Encode a finite subset by its binary incidence integer. -/
def encodeSet {n : Nat} (s : Finset (Fin n)) : Mask n :=
  ⟨(∑ i ∈ s, 2 ^ i.val) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

def EncodingOK (n : Nat) : Prop :=
  (∀ m : Mask n, encodeSet (decodeMask m) = m) ∧
  (∀ s : Finset (Fin n), decodeMask (encodeSet s) = s)

def singletonMask {n : Nat} (i : Fin n) : Mask n :=
  ⟨2 ^ i.val, Nat.pow_lt_pow_right (by decide) i.isLt⟩

theorem mem_decodeMask {n : Nat} (m : Mask n) (i : Fin n) :
    i ∈ decodeMask m ↔ m.val.testBit i.val = true := by
  simp [decodeMask]

theorem decodeMask_inter {n : Nat} (a b : Mask n) :
    decodeMask (a &&& b) = decodeMask a ∩ decodeMask b := by
  ext i
  simp [mem_decodeMask, Fin.and_val, Nat.testBit_and, Bool.and_eq_true]

theorem decodeMask_union {n : Nat} (a b : Mask n) :
    decodeMask (a ||| b) = decodeMask a ∪ decodeMask b := by
  ext i
  simp [mem_decodeMask, Fin.or_val_of_two_pow, Nat.testBit_or, Bool.or_eq_true]

theorem decodeMask_zero {n : Nat} : decodeMask (0 : Mask n) = ∅ := by
  ext i
  simp [mem_decodeMask]

theorem decodeMask_singleton {n : Nat} (i : Fin n) :
    decodeMask (singletonMask i) = {i} := by
  ext j
  simp [mem_decodeMask, singletonMask, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

theorem encodeSet_empty {n : Nat} : encodeSet (∅ : Finset (Fin n)) = 0 := by
  apply Fin.ext
  simp [encodeSet]

theorem encodeSet_union {n : Nat} (hok : EncodingOK n) (a b : Finset (Fin n)) :
    encodeSet (a ∪ b) = encodeSet a ||| encodeSet b := by
  have hi : Function.Injective (@decodeMask n) := Function.HasLeftInverse.injective ⟨encodeSet, hok.1⟩
  apply hi
  rw [decodeMask_union, hok.2, hok.2, hok.2]

theorem encodeSet_inter {n : Nat} (hok : EncodingOK n) (a b : Finset (Fin n)) :
    encodeSet (a ∩ b) = encodeSet a &&& encodeSet b := by
  have hi : Function.Injective (@decodeMask n) := Function.HasLeftInverse.injective ⟨encodeSet, hok.1⟩
  apply hi
  rw [decodeMask_inter, hok.2, hok.2, hok.2]

theorem encodeSet_singleton {n : Nat} (hok : EncodingOK n) (i : Fin n) :
    encodeSet ({i} : Finset (Fin n)) = singletonMask i := by
  have hi : Function.Injective (@decodeMask n) := Function.HasLeftInverse.injective ⟨encodeSet, hok.1⟩
  apply hi
  rw [hok.2, decodeMask_singleton]

theorem encodeSet_insert {n : Nat} (hok : EncodingOK n) (s : Finset (Fin n)) (i : Fin n) :
    encodeSet (insert i s) = encodeSet s ||| singletonMask i := by
  rw [← Finset.union_singleton, encodeSet_union hok, encodeSet_singleton hok]

end InfoE3
