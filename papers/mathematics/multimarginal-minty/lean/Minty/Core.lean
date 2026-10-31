import Mathlib

/-! Exact definitions for the three-marginal quadratic pairing on the real plane.
The coordinate model uses the ordinary Euclidean pairing, written explicitly.
The definition `CMonotone` is the actual two-point cost-swap definition.
-/
namespace Minty

abbrev Vec := Fin 2 → ℝ
abbrev Triple := Fin 3 → Vec

noncomputable def pairing (x y : Vec) : ℝ := x 0 * y 0 + x 1 * y 1

noncomputable def total (x : Triple) : Vec := x 0 + x 1 + x 2

noncomputable def cost (x : Triple) : ℝ :=
  pairing (x 0) (x 1) + pairing (x 0) (x 2) + pairing (x 1) (x 2)

noncomputable def mix (K : Finset (Fin 3)) (x y : Triple) : Triple :=
  fun i => if i ∈ K then x i else y i

noncomputable def Compatible (x y : Triple) : Prop :=
  ∀ i : Fin 3, 0 ≤ pairing (x i - y i) (total x - total y - (x i - y i))

noncomputable def CMonotone (S : Set Triple) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ K : Finset (Fin 3),
    cost (mix K x y) + cost (mix K y x) ≤ cost x + cost y

noncomputable def MaximalCMonotone (S : Set Triple) : Prop :=
  CMonotone S ∧ ∀ T : Set Triple, CMonotone T → S ⊆ T → T = S

end Minty
