import InfoE3.PositiveBase
import Mathlib.Data.Nat.Bitwise

namespace InfoE3

/-- Restrict an incidence vector to a consecutive block of m coordinates. -/
def sliceMask {n : Nat} (m shift : Nat) (S : Mask n) : Mask m :=
  ⟨(S.val >>> shift) % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩

theorem sliceMask_zero {n : Nat} (m shift : Nat) :
    sliceMask (n := n) m shift 0 = 0 := by
  apply Fin.ext
  simp [sliceMask]

theorem sliceMask_inter {n : Nat} (m shift : Nat) (A B : Mask n) :
    sliceMask m shift (A &&& B) = sliceMask m shift A &&& sliceMask m shift B := by
  apply Fin.ext
  simp only [sliceMask, Fin.and_val, Nat.shiftRight_and_distrib, Nat.and_mod_two_pow]

theorem sliceMask_union {n : Nat} (m shift : Nat) (A B : Mask n) :
    sliceMask m shift (A ||| B) = sliceMask m shift A ||| sliceMask m shift B := by
  apply Fin.ext
  simp only [sliceMask, Fin.or_val_of_two_pow, Nat.shiftRight_or_distrib,
    Nat.or_mod_two_pow]

theorem PMInt.slice {n m : Nat} {h : Mask m → ℤ} (hp : PMInt m h)
    (shift : Nat) : PMInt n (fun S => h (sliceMask m shift S)) := by
  constructor
  · rw [sliceMask_zero]
    exact hp.empty
  · intro a b hab
    apply hp.mono
    rw [← sliceMask_inter, hab]
  · intro a b
    rw [sliceMask_inter, sliceMask_union]
    exact hp.submod _ _

theorem PMInt.add {n : Nat} {h k : Mask n → ℤ}
    (hp : PMInt n h) (kp : PMInt n k) : PMInt n (fun S => h S + k S) := by
  constructor
  · simp [hp.empty, kp.empty]
  · intro a b hab
    exact add_le_add (hp.mono a b hab) (kp.mono a b hab)
  · intro a b
    have h1 := hp.submod a b
    have h2 := kp.submod a b
    linarith only [h1, h2]

end InfoE3
