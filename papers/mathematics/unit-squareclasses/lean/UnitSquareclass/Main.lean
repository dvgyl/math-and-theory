import UnitSquareclass.Geometry
import UnitSquareclass.Arithmetic
import UnitSquareclass.IntegralReflections
import UnitSquareclass.Helpers

/-!
# Represented unit squareclasses over a totally real number field

The geometric shell hypotheses are proved here from the actual arithmetic lattice.
The units are units of the actual ring of integers, and distinctness is modulo
squares of that unit group. The all-embeddings hypotheses express total reality
and total positive definiteness explicitly.
-/

noncomputable section

open NumberField
open scoped NumberField
open LinearMap (BilinForm)

namespace UnitSquareclass

variable {K V I J : Type*} [Field K] [NumberField K]
  [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype I]

/-- The number-field unit-squareclass bound, with a finite generating family exposed. -/
theorem represented_unit_squareclasses_card_le_finrank_of_generators
    [Fintype J]
    (L : Submodule (𝓞 K) V)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0)
    (hp : ∀ (φ : K →+* ℂ) (z : V), z ≠ 0 → 0 < (φ (B z z)).re)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (e : J → V) (he : ∀ j, e j ∈ L)
    (hspan : ∀ x ∈ L, x ∈ Submodule.span K (Set.range e))
    (u : I → (𝓞 K)ˣ)
    (hrep : ∀ i, ∃ x ∈ L, B x x = ((u i : 𝓞 K) : K))
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    Fintype.card I ≤ Module.finrank K V := by
  classical
  have ha : ∀ z : V, B z z = 0 → z = 0 := by
    intro z hz
    apply Classical.byContradiction
    intro hzne
    have hpz := hpos z hzne
    rw [hz] at hpz
    exact (lt_irrefl 0) hpz
  have hfinite : ∀ i, {x : V | x ∈ L ∧ B x x = ((u i : 𝓞 K) : K)}.Finite := by
    intro i
    apply finite_arithmetic_shell B hB ha hr hp (L : Set V) e hspan
    intro x hx j
    exact two_mul_bilin_isIntegral L B hB hQ hx (he j)
  let S : I → Finset V := fun i => (hfinite i).toFinset
  have hmem : ∀ i x, x ∈ S i ↔ x ∈ L ∧ B x x = ((u i : 𝓞 K) : K) := by
    intro i x
    exact (hfinite i).mem_toFinset
  apply finite_reflection_shells_card_le_finrank B hB hpos S
  · intro i
    obtain ⟨x, hx, hxnorm⟩ := hrep i
    exact ⟨x, (hmem i x).mpr ⟨hx, hxnorm⟩⟩
  · intro i x hx hxzero
    have hxnorm := ((hmem i x).mp hx).2
    have hu0 : ((u i : 𝓞 K) : K) ≠ 0 :=
      (RingOfIntegers.coe_ne_zero_iff (K := K)).2 (u i).ne_zero
    apply hu0
    simpa [hxzero] using hxnorm.symm
  · intro i x hx
    apply (hmem i (-x)).mpr
    exact neg_mem_integralShell L B _ ((hmem i x).mp hx)
  · intro i j x hx y hy
    apply (hmem j _).mpr
    have hrxy := integralReflect_mem_shell L B hB hQ (u i)
      ((u j : 𝓞 K) : K) ((hmem i x).mp hx) ((hmem j y).mp hy)
    simpa only [reflect, integralReflect] using hrxy
  · intro i j hij x hx y hy a hxy
    obtain ⟨w, hw⟩ := collinear_unit_values_same_squareclass B (u i) (u j) x y
      ((hmem i x).mp hx).2 ((hmem j y).mp hy).2 a hxy
    exact hclasses i j hij w hw

/-- A finitely generated integral lattice represents at most the ambient dimension
many distinct squareclasses of ring-of-integers units. No classicality assumption is used. -/
theorem represented_unit_squareclasses_card_le_finrank
    (L : Submodule (𝓞 K) V) (hfg : L.FG)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0)
    (hp : ∀ (φ : K →+* ℂ) (z : V), z ≠ 0 → 0 < (φ (B z z)).re)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (u : I → (𝓞 K)ˣ)
    (hrep : ∀ i, ∃ x ∈ L, B x x = ((u i : 𝓞 K) : K))
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    Fintype.card I ≤ Module.finrank K V := by
  obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine represented_unit_squareclasses_card_le_finrank_of_generators
    L B hB hpos hr hp hQ e ?_ ?_ u hrep hclasses
  · intro j
    rw [← he]
    exact Submodule.subset_span ⟨j, rfl⟩
  · intro x hx
    apply Submodule.span_le_restrictScalars (𝓞 K) K (Set.range e)
    rwa [he]

/-- The intrinsic rank version: the bound is the dimension of the field-span of the lattice. -/
theorem represented_unit_squareclasses_card_le_lattice_rank
    (L : Submodule (𝓞 K) V) (hfg : L.FG)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
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
  have hmap : L'.map f = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
  have hfg' : L'.FG := by
    apply Submodule.fg_of_fg_map_injective f (fun x y hxy => Subtype.ext hxy)
    rwa [hmap]
  have hne : ∀ x : W, x ≠ 0 → (x : V) ≠ 0 := by
    intro x hx hzero
    exact hx (Subtype.ext hzero)
  let B' : BilinForm K W := B.restrict W
  have hB' : B'.IsSymm := by
    intro x y
    exact hB x y
  have hpos' : ∀ z : W, z ≠ 0 → 0 < B' z z := by
    intro z hz
    exact hpos z (hne z hz)
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
  exact represented_unit_squareclasses_card_le_finrank
    L' hfg' B' hB' hpos' hr hp' hQ' u hrep' hclasses

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The ambient-dimension theorem with the field ordering constructed from an embedding. -/
theorem represented_unit_squareclasses_card_le_finrank_of_real_embeddings
    (L : Submodule (𝓞 K) V) (hfg : L.FG)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0)
    (hp : ∀ (φ : K →+* ℂ) (z : V), z ≠ 0 → 0 < (φ (B z z)).re)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (u : I → (𝓞 K)ˣ)
    (hrep : ∀ i, ∃ x ∈ L, B x x = ((u i : 𝓞 K) : K))
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    Fintype.card I ≤ Module.finrank K V := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  let ψ := realEmbeddingOfRealImage φ (hr φ)
  letI : LinearOrder K := realEmbeddingLinearOrder ψ
  letI : IsStrictOrderedRing K := realEmbeddingStrictOrderedRing ψ
  have hpos : ∀ z : V, z ≠ 0 → 0 < B z z := by
    intro z hz
    change ψ 0 < ψ (B z z)
    rw [map_zero]
    exact hp φ z hz
  exact represented_unit_squareclasses_card_le_finrank
    L hfg B hB hpos hr hp hQ u hrep hclasses

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The intrinsic lattice-rank theorem, independent of a supplied ordering. -/
theorem represented_unit_squareclasses_card_le_lattice_rank_of_real_embeddings
    (L : Submodule (𝓞 K) V) (hfg : L.FG)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0)
    (hp : ∀ (φ : K →+* ℂ) (z : V), z ≠ 0 → 0 < (φ (B z z)).re)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (u : I → (𝓞 K)ˣ)
    (hrep : ∀ i, ∃ x ∈ L, B x x = ((u i : 𝓞 K) : K))
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    Fintype.card I ≤ Module.finrank K (Submodule.span K (L : Set V)) := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  let ψ := realEmbeddingOfRealImage φ (hr φ)
  letI : LinearOrder K := realEmbeddingLinearOrder ψ
  letI : IsStrictOrderedRing K := realEmbeddingStrictOrderedRing ψ
  have hpos : ∀ z : V, z ≠ 0 → 0 < B z z := by
    intro z hz
    change ψ 0 < ψ (B z z)
    rw [map_zero]
    exact hp φ z hz
  exact represented_unit_squareclasses_card_le_lattice_rank
    L hfg B hB hpos hr hp hQ u hrep hclasses

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A totally real number field's integral positive-definite lattice represents at
most its rank many unit squareclasses. Positivity is required at every real embedding. -/
theorem totally_real_represented_unit_squareclasses_card_le_lattice_rank
    [NumberField.IsTotallyReal K]
    (L : Submodule (𝓞 K) V) (hfg : L.FG)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hp : ∀ (φ : K →+* ℝ) (z : V), z ≠ 0 → 0 < φ (B z z))
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (u : I → (𝓞 K)ˣ)
    (hrep : ∀ i, ∃ x ∈ L, B x x = ((u i : 𝓞 K) : K))
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    Fintype.card I ≤ Module.finrank K (Submodule.span K (L : Set V)) := by
  have hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0 := by
    intro φ a
    have hφ := NumberField.InfinitePlace.isReal_of_mk_isReal
      (NumberField.IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ))
    exact Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ a)
  have hp' : ∀ (φ : K →+* ℂ) (z : V), z ≠ 0 → 0 < (φ (B z z)).re := by
    intro φ z hz
    exact hp (realEmbeddingOfRealImage φ (hr φ)) z hz
  exact represented_unit_squareclasses_card_le_lattice_rank_of_real_embeddings
    L hfg B hB hr hp' hQ u hrep hclasses

end UnitSquareclass

#print axioms UnitSquareclass.represented_unit_squareclasses_card_le_finrank
#print axioms UnitSquareclass.represented_unit_squareclasses_card_le_lattice_rank
#print axioms UnitSquareclass.represented_unit_squareclasses_card_le_finrank_of_real_embeddings
#print axioms UnitSquareclass.totally_real_represented_unit_squareclasses_card_le_lattice_rank
