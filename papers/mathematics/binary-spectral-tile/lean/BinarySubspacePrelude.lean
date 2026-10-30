import BinaryBasic
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false
namespace BinaryFuglede

lemma finrank_three_has_cube (H : Submodule (ZMod 2) V)
    (hfin : Module.finrank (ZMod 2) H = 3) :
    ∃ a b c : V, a ∈ H ∧ b ∈ H ∧ c ∈ H ∧
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b ≠ 0 ∧ a + c ≠ 0 ∧
      b + c ≠ 0 ∧ a + b + c ≠ 0 := by
  let B := Module.finBasisOfFinrankEq (ZMod 2) H hfin
  refine ⟨B 0, B 1, B 2, (B 0).property, (B 1).property, (B 2).property,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    exact B.ne_zero 0 (Subtype.ext hz)
  · intro hz
    exact B.ne_zero 1 (Subtype.ext hz)
  · intro hz
    exact B.ne_zero 2 (Subtype.ext hz)
  · intro hz
    have h := congrArg (fun z : H => B.repr z 0)
      (show B 0 + B 1 = 0 from Subtype.ext hz)
    simp at h
  · intro hz
    have h := congrArg (fun z : H => B.repr z 0)
      (show B 0 + B 2 = 0 from Subtype.ext hz)
    simp at h
  · intro hz
    have h := congrArg (fun z : H => B.repr z 1)
      (show B 1 + B 2 = 0 from Subtype.ext hz)
    simp at h
  · intro hz
    have h := congrArg (fun z : H => B.repr z 0)
      (show B 0 + B 1 + B 2 = 0 from Subtype.ext hz)
    simp at h

end BinaryFuglede
