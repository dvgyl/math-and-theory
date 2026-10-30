import UnitSquareclass.Main
import UnitSquareclass.FieldDescent
import UnitSquareclass.DescentUnits

/-!
# Explicit finite-subfield descent for represented integer-unit squareclasses

The smaller field, quadratic form, lattice and unit representatives are constructed,
rather than supplied as assumptions.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

open NumberField
open scoped NumberField BigOperators
open LinearMap (BilinForm)

namespace UnitSquareclass

variable {K V N : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [Fintype N] [DecidableEq N]

/-- Coordinate extension along the actual intermediate-field inclusion. -/
def subfieldLift (b : Basis N K V) (F : IntermediateField ℚ K) (x : N → F) : V :=
  b.equivFun.symm (fun j => (x j : K))

theorem subfieldLift_injective (b : Basis N K V) (F : IntermediateField ℚ K) :
    Function.Injective (subfieldLift b F) := by
  intro x y hxy
  have h := b.equivFun.symm.injective hxy
  funext j
  exact Subtype.ext (congrFun h j)

@[simp] theorem subfieldLift_zero (b : Basis N K V) (F : IntermediateField ℚ K) :
    subfieldLift b F 0 = 0 := by
  simp [subfieldLift]

@[simp] theorem subfieldLift_add (b : Basis N K V) (F : IntermediateField ℚ K)
    (x y : N → F) :
    subfieldLift b F (x + y) = subfieldLift b F x + subfieldLift b F y := by
  change b.equivFun.symm ((fun j => (x j : K)) + (fun j => (y j : K))) = _
  exact map_add _ _ _

@[simp] theorem subfieldLift_smul (b : Basis N K V) (F : IntermediateField ℚ K)
    (a : F) (x : N → F) :
    subfieldLift b F (a • x) = (a : K) • subfieldLift b F x := by
  change b.equivFun.symm ((a : K) • (fun j => (x j : K))) = _
  exact map_smul _ _ _

/-- Restriction of the Gram matrix to a field containing all its entries. -/
def subfieldBilin (b : Basis N K V) (F : IntermediateField ℚ K)
    (B : BilinForm K V) (hG : ∀ j k, B (b j) (b k) ∈ F) :
    BilinForm F (N → F) :=
  Matrix.toBilin' (fun j k => ⟨B (b j) (b k), hG j k⟩)

/-- The restricted Gram form agrees with the original form under coordinate extension. -/
theorem subfieldBilin_coe (b : Basis N K V) (F : IntermediateField ℚ K)
    (B : BilinForm K V) (hG : ∀ j k, B (b j) (b k) ∈ F) (x y : N → F) :
    (subfieldBilin b F B hG x y : K) =
      B (subfieldLift b F x) (subfieldLift b F y) := by
  change F.val (Matrix.toBilin' (fun j k => ⟨B (b j) (b k), hG j k⟩) x y) = _
  conv_rhs =>
    simp only [subfieldLift, Basis.equivFun_symm_apply]
    rw [BilinForm.sum_left]
    simp only [BilinForm.sum_right, BilinForm.smul_left, BilinForm.smul_right, Finset.mul_sum]
  rw [Matrix.toBilin'_apply]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  change (x j : K) * B (b j) (b k) * (y k : K) =
    (y k : K) * ((x j : K) * B (b j) (b k))
  ring

theorem subfieldBilin_symm (b : Basis N K V) (F : IntermediateField ℚ K)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hG : ∀ j k, B (b j) (b k) ∈ F) :
    (subfieldBilin b F B hG).IsSymm := by
  intro x y
  apply Subtype.ext
  change (subfieldBilin b F B hG x y : K) =
    (subfieldBilin b F B hG y x : K)
  rw [subfieldBilin_coe, subfieldBilin_coe]
  exact hB _ _

/-- Algebraic integrality descends through the actual intermediate-field inclusion. -/
theorem isIntegral_subfield_iff (F : IntermediateField ℚ K) (a : F) :
    IsIntegral ℤ (a : K) ↔ IsIntegral ℤ a :=
  isIntegral_algHom_iff (F.val.restrictScalars ℤ) F.val.injective

/-- A represented integer unit, when its value belongs to F, is an actual O_F-unit. -/
def subfieldUnit (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ)
    (hu : ((u : 𝓞 K) : K) ∈ F) : (𝓞 F)ˣ := by
  have hui : (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) ∈ F := by
    rw [coe_integral_unit_inv]
    exact F.inv_mem hu
  let a : F := ⟨((u : 𝓞 K) : K), hu⟩
  let c : F := ⟨(((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K), hui⟩
  have ha : IsIntegral ℤ a :=
    (isIntegral_subfield_iff F a).mp (RingOfIntegers.isIntegral_coe (u : 𝓞 K))
  have hc : IsIntegral ℤ c :=
    (isIntegral_subfield_iff F c).mp
      (RingOfIntegers.isIntegral_coe ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
  let aO : 𝓞 F := ⟨a, ha⟩
  let cO : 𝓞 F := ⟨c, hc⟩
  have hac : aO * cO = 1 := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    change ((u : 𝓞 K) : K) * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1
    change (algebraMap (𝓞 K) K) (u : 𝓞 K) *
      (algebraMap (𝓞 K) K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1
    rw [← map_mul]
    simp
  exact Units.mkOfMulEqOne aO cO hac

theorem subfieldUnit_coe (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ)
    (hu : ((u : 𝓞 K) : K) ∈ F) :
    ((((subfieldUnit F u hu : (𝓞 F)ˣ) : 𝓞 F) : F) : K) =
      ((u : 𝓞 K) : K) := rfl

/-- Mapping the descended actual integer unit back recovers the original unit. -/
theorem subfieldUnit_map (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ)
    (hu : ((u : 𝓞 K) : K) ∈ F) :
    Units.map (RingOfIntegers.mapRingHom F.val).toMonoidHom
      (subfieldUnit F u hu) = u := by
  apply Units.ext
  apply RingOfIntegers.ext
  rfl

/-- Coordinates restrict whenever their finitely many values belong to F. -/
def subfieldCoords (b : Basis N K V) (F : IntermediateField ℚ K)
    (x : V) (hx : ∀ j, b.repr x j ∈ F) : N → F :=
  fun j => ⟨b.repr x j, hx j⟩

theorem subfieldLift_coords (b : Basis N K V) (F : IntermediateField ℚ K)
    (x : V) (hx : ∀ j, b.repr x j ∈ F) :
    subfieldLift b F (subfieldCoords b F x hx) = x := by
  exact b.equivFun.symm_apply_apply x


variable {I : Type*} [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- The actual O_F-span of coordinates lifts into the original integral lattice. -/
theorem subfieldLift_span_mem (L : Submodule (𝓞 K) V)
    (b : Basis N K V) (F : IntermediateField ℚ K)
    (z : I → N → F) (hz : ∀ i, subfieldLift b F (z i) ∈ L) :
    ∀ x ∈ Submodule.span (𝓞 F) (Set.range z), subfieldLift b F x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hz i
  | zero => simpa only [subfieldLift_zero] using L.zero_mem
  | add x y _ _ hx hy =>
      rw [subfieldLift_add]
      exact L.add_mem hx hy
  | smul a x _ hx =>
      have hs : a • x = (algebraMap (𝓞 F) F a) • x :=
        (IsScalarTower.algebraMap_smul F a x).symm
      rw [hs, subfieldLift_smul]
      let k : 𝓞 K := RingOfIntegers.mapRingHom F.val a
      have hk : ((algebraMap (𝓞 F) F a : F) : K) =
          algebraMap (𝓞 K) K k := rfl
      rw [hk, IsScalarTower.algebraMap_smul K]
      exact L.smul_mem k hx



/-- Over an arbitrary algebraic totally real field, an integral positive-definite
lattice represents at most the ambient dimension many actual integer-unit squareclasses.
No finite-generation hypothesis on the ambient lattice is required: the finite
representatives are explicitly descended to a finitely generated number-field lattice. -/
theorem algebraic_represented_unit_squareclasses_card_le_finrank
    [Algebra.IsAlgebraic ℚ K] [FiniteDimensional K V] [Fintype I]
    (L : Submodule (𝓞 K) V)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0)
    (hp : ∀ (φ : K →+* ℂ) (z : V), z ≠ 0 → 0 < (φ (B z z)).re)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (u : I → (𝓞 K)ˣ)
    (hrep : ∀ i, ∃ x ∈ L, B x x = ((u i : 𝓞 K) : K))
    (hclasses : ∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i) :
    Fintype.card I ≤ Module.finrank K V := by
  classical
  choose v hv hnorm using hrep
  let b := Module.finBasis K V
  let sG : Finset K := Finset.univ.image
    (fun jk : Fin (Module.finrank K V) × Fin (Module.finrank K V) =>
      B (b jk.1) (b jk.2))
  let sV : Finset K := Finset.univ.image
    (fun ij : I × Fin (Module.finrank K V) => b.repr (v ij.1) ij.2)
  let sU : Finset K := Finset.univ.image (fun i => ((u i : 𝓞 K) : K))
  obtain ⟨F, hF, hS⟩ := exists_numberField_containing (sG ∪ (sV ∪ sU))
  letI : NumberField F := hF
  have hG : ∀ j k, B (b j) (b k) ∈ F := by
    intro j k
    apply hS
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩
  have hV : ∀ i j, b.repr (v i) j ∈ F := by
    intro i j
    apply hS
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
  have hU : ∀ i, ((u i : 𝓞 K) : K) ∈ F := by
    intro i
    apply hS
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let z : I → Fin (Module.finrank K V) → F :=
    fun i => subfieldCoords b F (v i) (hV i)
  let L' : Submodule (𝓞 F) (Fin (Module.finrank K V) → F) :=
    Submodule.span (𝓞 F) (Set.range z)
  let B' := subfieldBilin b F B hG
  let u' : I → (𝓞 F)ˣ := fun i => subfieldUnit F (u i) (hU i)
  have hfg : L'.FG := Submodule.fg_span (Set.finite_range z)
  have hz : ∀ i, subfieldLift b F (z i) = v i := by
    intro i
    exact subfieldLift_coords b F (v i) (hV i)
  have hL : ∀ x ∈ L', subfieldLift b F x ∈ L :=
    subfieldLift_span_mem L b F z (fun i => by rw [hz]; exact hv i)
  have hB' : B'.IsSymm := subfieldBilin_symm b F B hB hG
  have hr' : ∀ (φ : F →+* ℂ) (a : F), (φ a).im = 0 :=
    totally_real_intermediate F hr
  have hp' : ∀ (φ : F →+* ℂ) (x : Fin (Module.finrank K V) → F),
      x ≠ 0 → 0 < (φ (B' x x)).re := by
    intro φ x hx
    apply positive_intermediate F (B' x x) _ φ
    intro ψ
    rw [subfieldBilin_coe]
    apply hp ψ
    intro hzero
    apply hx
    apply subfieldLift_injective b F
    simpa only [subfieldLift_zero] using hzero
  have hQ' : ∀ x ∈ L', IsIntegral ℤ (B' x x) := by
    intro x hx
    apply (isIntegral_subfield_iff F (B' x x)).mp
    rw [subfieldBilin_coe]
    exact hQ _ (hL x hx)
  have hrep' : ∀ i, ∃ x ∈ L', B' x x = ((u' i : 𝓞 F) : F) := by
    intro i
    refine ⟨z i, Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    apply Subtype.ext
    change (B' (z i) (z i) : K) = (((u' i : 𝓞 F) : F) : K)
    rw [subfieldBilin_coe, hz]
    exact hnorm i
  have hclasses' : ∀ i j, i ≠ j → ∀ w : (𝓞 F)ˣ, u' j ≠ w ^ 2 * u' i :=
    distinct_unit_squareclasses_descend F u u'
      (fun i => subfieldUnit_map F (u i) (hU i)) hclasses
  have hbound := represented_unit_squareclasses_card_le_finrank_of_real_embeddings
    L' hfg B' hB' hr' hp' hQ' u' hrep' hclasses'
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hbound

end UnitSquareclass

#print axioms UnitSquareclass.algebraic_represented_unit_squareclasses_card_le_finrank

