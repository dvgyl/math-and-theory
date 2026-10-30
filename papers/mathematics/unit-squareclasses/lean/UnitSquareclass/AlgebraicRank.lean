import UnitSquareclass.Descent

/-!
# The intrinsic rank bound over arbitrary algebraic totally real fields

The dimension in the conclusion is the dimension of the field-span of the
actual integral module. Neither freeness nor finite generation of that module
is needed, and the ambient algebraic field can have infinite degree.
-/

noncomputable section

open NumberField
open scoped NumberField
open LinearMap (BilinForm)

namespace UnitSquareclass

variable {K V I : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype I]

/-- An integral totally positive-definite module over any algebraic totally real
field represents at most its rank many actual ring-of-integers unit squareclasses. -/
theorem algebraic_represented_unit_squareclasses_card_le_lattice_rank
    (L : Submodule (𝓞 K) V)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0)
    (hp : ∀ (φ : K →+* ℂ) (z : V), z ≠ 0 → 0 < (φ (B z z)).re)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (u : I → (𝓞 K)ˣ)
    (hrep : ∀ i, ∃ x ∈ L, B x x = ((u i : 𝓞 K) : K))
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    Fintype.card I ≤ Module.finrank K (Submodule.span K (L : Set V)) := by
  let W := Submodule.span K (L : Set V)
  let f : W →ₗ[𝓞 K] V := W.subtype.restrictScalars (𝓞 K)
  let L' : Submodule (𝓞 K) W := L.comap f
  have hne : ∀ x : W, x ≠ 0 → (x : V) ≠ 0 := by
    intro x hx hzero
    exact hx (Subtype.ext hzero)
  let B' : BilinForm K W := B.restrict W
  have hB' : B'.IsSymm := by
    intro x y
    exact hB x y
  have hp' : ∀ (φ : K →+* ℂ) (z : W), z ≠ 0 → 0 < (φ (B' z z)).re := by
    intro φ z hz
    exact hp φ z (hne z hz)
  have hQ' : ∀ x ∈ L', IsIntegral ℤ (B' x x) := by
    intro x hx
    exact hQ x hx
  have hrep' : ∀ i, ∃ x ∈ L', B' x x = ((u i : 𝓞 K) : K) := by
    intro i
    obtain ⟨x, hx, hnorm⟩ := hrep i
    exact ⟨⟨x, Submodule.subset_span hx⟩, hx, hnorm⟩
  exact algebraic_represented_unit_squareclasses_card_le_finrank
    L' B' hB' hr hp' hQ' u hrep' hclasses

end UnitSquareclass

#print axioms UnitSquareclass.algebraic_represented_unit_squareclasses_card_le_lattice_rank
