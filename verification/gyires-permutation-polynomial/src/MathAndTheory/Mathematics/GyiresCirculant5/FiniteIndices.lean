module

/- See PROVENANCE.md for source attribution and modifications. -/

public import Mathlib.Data.Fin.Basic

/-!
# Numerals in `Fin 5`

Normal forms for a few numerals and negations in `Fin 5`, used by `simp`.
-/

@[expose] public section

namespace MathAndTheory.GyiresCirculant5
@[simp] theorem fin5_mk_two : (⟨2, by decide⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_three : (⟨3, by decide⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_four : (⟨4, by decide⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin5_value_two : (2 : Fin 5).val = 2 := rfl
@[simp] theorem fin5_value_three : (3 : Fin 5).val = 3 := rfl
@[simp] theorem fin5_value_four : (4 : Fin 5).val = 4 := rfl
@[simp] theorem fin5_negative_one : (-1 : Fin 5) = 4 := by decide
@[simp] theorem fin5_negative_two : (-2 : Fin 5) = 3 := by decide
@[simp] theorem fin5_negative_three : (-3 : Fin 5) = 2 := by decide
@[simp] theorem fin5_negative_four : (-4 : Fin 5) = 1 := by decide
end MathAndTheory.GyiresCirculant5
