import InfoE3.Encoding
import InfoE3.LocalToGlobal

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace InfoE3

def MaskLocalMono {n : Nat} (h : Mask n → ℤ) : Prop :=
  ∀ m : Mask n, ∀ i : Fin n, m.val.testBit i.val = false →
    h m ≤ h (m ||| singletonMask i)

def MaskLocalSquares {n : Nat} (h : Mask n → ℤ) : Prop :=
  ∀ m : Mask n, ∀ i j : Fin n,
    m.val.testBit i.val = false → m.val.testBit j.val = false → i ≠ j →
    h m + h ((m ||| singletonMask j) ||| singletonMask i) ≤
      h (m ||| singletonMask i) + h (m ||| singletonMask j)

theorem encodeSet_notMem {n : Nat} (hok : EncodingOK n)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    (encodeSet S).val.testBit i.val = false := by
  cases hb : (encodeSet S).val.testBit i.val
  · rfl
  · have hm := (mem_decodeMask (encodeSet S) i).mpr hb
    rw [hok.2] at hm
    exact (hi hm).elim

/-- Local numerical checks imply every inequality in the full PMInt definition. -/
theorem PMInt.of_local {n : Nat} {h : Mask n → ℤ}
    (hok : EncodingOK n) (hzero : h 0 = 0)
    (hm : MaskLocalMono h) (hs : MaskLocalSquares h) : PMInt n h := by
  let f : Finset (Fin n) → ℤ := fun S => h (encodeSet S)
  have hmono : ∀ S i, i ∉ S → f S ≤ f (insert i S) := by
    intro S i hi
    dsimp [f]
    rw [encodeSet_insert hok]
    exact hm _ _ (encodeSet_notMem hok S i hi)
  have hsquare : LocalSquares f := by
    intro S i j hi hj hij
    dsimp [f]
    simp only [encodeSet_insert hok]
    exact hs _ _ _ (encodeSet_notMem hok S i hi) (encodeSet_notMem hok S j hj) hij
  constructor
  · exact hzero
  · intro a b hab
    have hsub : decodeMask a ⊆ decodeMask b := by
      apply Finset.inter_eq_left.mp
      rw [← decodeMask_inter, hab]
    have hh := monotone_of_singleton_steps hmono (decodeMask a) (decodeMask b) hsub
    simpa only [f, hok.1] using hh
  · intro a b
    have hh := hsquare.submodular (decodeMask a) (decodeMask b)
    dsimp [f] at hh
    rw [encodeSet_inter hok, encodeSet_union hok, hok.1, hok.1] at hh
    exact hh

#print axioms PMInt.of_local
end InfoE3
