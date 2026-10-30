import UnitSquareclass.IntegralReflections

/-! Actual integral-unit squareclasses and integral spans under intermediate-field descent. -/

noncomputable section

open NumberField
open scoped NumberField

namespace UnitSquareclass

variable {K I V W : Type*} [Field K] [CharZero K]

/-- Distinct unit squareclasses remain distinct after descent to an intermediate field. -/
theorem distinct_unit_squareclasses_descend
    (F : IntermediateField ℚ K)
    (u : I → (𝓞 K)ˣ) (v : I → (𝓞 F)ˣ)
    (hmap : ∀ i, Units.map (RingOfIntegers.mapRingHom F.val).toMonoidHom (v i) = u i)
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    ∀ i j, i ≠ j → ∀ w : (𝓞 F)ˣ, v j ≠ w ^ 2 * v i := by
  intro i j hij w heq
  let f := Units.map (RingOfIntegers.mapRingHom F.val).toMonoidHom
  apply hclasses i j hij (f w)
  have heq' := congrArg f heq
  simpa only [map_mul, map_pow, hmap, f] using heq'

/-- An additive map compatible with integral scalar inclusion maps the generated
O_F-submodule into an O_K-lattice as soon as it maps the generators into it. -/
theorem integral_span_maps_into_lattice
    [AddCommGroup V] [Module (𝓞 K) V]
    (F : IntermediateField ℚ K)
    [AddCommGroup W] [Module (𝓞 F) W]
    (L : Submodule (𝓞 K) V) (g : W → V)
    (hzero : g 0 = 0)
    (hadd : ∀ x y, g (x + y) = g x + g y)
    (hsmul : ∀ (a : 𝓞 F) (x : W),
      g (a • x) = (RingOfIntegers.mapRingHom F.val a) • g x)
    (s : Set W) (hs : ∀ x ∈ s, g x ∈ L) :
    ∀ x ∈ Submodule.span (𝓞 F) s, g x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simpa only [hzero] using L.zero_mem
  | add x y _ _ hx hy =>
      rw [hadd]
      exact L.add_mem hx hy
  | smul a x _ hx =>
      rw [hsmul]
      exact L.smul_mem _ hx

end UnitSquareclass

#print axioms UnitSquareclass.distinct_unit_squareclasses_descend
#print axioms UnitSquareclass.integral_span_maps_into_lattice
