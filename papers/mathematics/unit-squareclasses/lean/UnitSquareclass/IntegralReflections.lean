import Mathlib

/-!
# Arithmetic unit reflections over the actual ring of integers

These lemmas do not assume a classical (integral half-polar) lattice.
Only the diagonal values of the symmetric bilinear form are integral.
The scalar field need not be a finite number field for these algebraic lemmas.
-/

noncomputable section

open NumberField
open scoped NumberField
open LinearMap (BilinForm)

namespace UnitSquareclass

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The explicit arithmetic reflection, matching the geometric formula. -/
def integralReflect (B : BilinForm K V) (v x : V) : V :=
  x - (2 * B v x / B v v) • v

/-- Inverting an actual ring-of-integers unit agrees with inversion in the field. -/
theorem coe_integral_unit_inv (u : (𝓞 K)ˣ) :
    (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = (((u : 𝓞 K) : K))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change (algebraMap (𝓞 K) K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
    (algebraMap (𝓞 K) K) (u : 𝓞 K) = 1
  rw [← map_mul]
  simp

/-- A field square root of a ring-of-integers unit is itself an integer unit. -/
theorem exists_integral_unit_of_sq_eq (u : (𝓞 K)ˣ) (c : K)
    (hc : c ^ 2 = ((u : 𝓞 K) : K)) :
    ∃ w : (𝓞 K)ˣ, ((w : 𝓞 K) : K) = c ∧ w ^ 2 = u := by
  have hc0 : c ≠ 0 := by
    intro h
    have hu0 := (RingOfIntegers.coe_ne_zero_iff (K := K)).2 u.ne_zero
    apply hu0
    change ((u : 𝓞 K) : K) = 0
    rw [← hc, h, zero_pow (by decide : 2 ≠ 0)]
  have hint : IsIntegral ℤ c := IsIntegral.of_pow (n := 2) (by decide) (by
    rw [hc]
    exact RingOfIntegers.isIntegral_coe (u : 𝓞 K))
  have hinv : IsIntegral ℤ c⁻¹ := IsIntegral.of_pow (n := 2) (by decide) (by
    rw [inv_pow, hc, ← coe_integral_unit_inv u]
    exact RingOfIntegers.isIntegral_coe ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
  let a : 𝓞 K := ⟨c, hint⟩
  let b : 𝓞 K := ⟨c⁻¹, hinv⟩
  have hab : a * b = 1 := by
    apply RingOfIntegers.ext
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc0
  let w : (𝓞 K)ˣ := Units.mkOfMulEqOne a b hab
  refine ⟨w, rfl, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  change c ^ 2 = ((u : 𝓞 K) : K)
  exact hc

/-- If the ratio of two integral units is a field square, it is an integral-unit square. -/
theorem exists_integral_unit_of_ratio_sq (u v : (𝓞 K)ˣ) (c : K)
    (hc : ((v : 𝓞 K) : K) = c ^ 2 * ((u : 𝓞 K) : K)) :
    ∃ w : (𝓞 K)ˣ, v = w ^ 2 * u := by
  have hu0 : ((u : 𝓞 K) : K) ≠ 0 :=
    (RingOfIntegers.coe_ne_zero_iff (K := K)).2 u.ne_zero
  have hs : c ^ 2 = (((v * u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := by
    change c ^ 2 = (algebraMap (𝓞 K) K)
      ((v : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
    rw [map_mul]
    change c ^ 2 = ((v : 𝓞 K) : K) * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)
    rw [coe_integral_unit_inv, hc]
    field_simp
  obtain ⟨w, -, hw⟩ := exists_integral_unit_of_sq_eq (v * u⁻¹) c hs
  refine ⟨w, ?_⟩
  rw [hw]
  simp [mul_assoc]

section Lattice

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [IsScalarTower (𝓞 K) K V] in
/-- Diagonal integrality implies integrality of twice the symmetric bilinear pairing. -/
theorem two_mul_bilin_isIntegral (L : Submodule (𝓞 K) V)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    {v x : V} (hv : v ∈ L) (hx : x ∈ L) :
    IsIntegral ℤ (2 * B v x) := by
  have h := ((hQ (v + x) (L.add_mem hv hx)).sub (hQ v hv)).sub (hQ x hx)
  have heq : B (v + x) (v + x) - B v v - B x x = 2 * B v x := by
    simp only [BilinForm.add_left, BilinForm.add_right, ← hB v x, RingHom.id_apply]
    ring
  rwa [heq] at h

/-- A reflection in a vector of integral-unit norm preserves the actual O_K-submodule. -/
theorem integralReflect_mem (L : Submodule (𝓞 K) V)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    {v x : V} (hv : v ∈ L) (hx : x ∈ L)
    (u : (𝓞 K)ˣ) (hu : B v v = ((u : 𝓞 K) : K)) :
    integralReflect B v x ∈ L := by
  let a : 𝓞 K := ⟨2 * B v x, two_mul_bilin_isIntegral L B hB hQ hv hx⟩
  let b : 𝓞 K := a * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
  have hb : (b : K) = 2 * B v x / B v v := by
    change (algebraMap (𝓞 K) K) (a * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) = _
    rw [map_mul]
    change (a : K) * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = _
    rw [coe_integral_unit_inv, hu]
    simp [a, div_eq_mul_inv]
  have hm : (2 * B v x / B v v) • v ∈ L := by
    rw [← hb]
    change (algebraMap (𝓞 K) K b) • v ∈ L
    rw [IsScalarTower.algebraMap_smul K]
    exact L.smul_mem b hv
  exact L.sub_mem hx hm

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/-- The diagonal value is unchanged by the explicit unit reflection. -/
theorem integralReflect_norm (B : BilinForm K V) (hB : B.IsSymm)
    (v x : V) (hv : B v v ≠ 0) :
    B (integralReflect B v x) (integralReflect B v x) = B x x := by
  unfold integralReflect
  simp only [BilinForm.sub_left, BilinForm.sub_right,
    BilinForm.smul_left, BilinForm.smul_right, ← hB v x, RingHom.id_apply]
  field_simp
  ring

omit [IsScalarTower (𝓞 K) K V] in
/-- Negation preserves a fixed quadratic-value shell of the O_K-submodule. -/
theorem neg_mem_integralShell (L : Submodule (𝓞 K) V)
    (B : BilinForm K V) (u : K) {x : V}
    (hx : x ∈ L ∧ B x x = u) :
    -x ∈ L ∧ B (-x) (-x) = u := by
  refine ⟨L.neg_mem hx.1, ?_⟩
  simpa only [BilinForm.neg_left, BilinForm.neg_right, neg_neg] using hx.2

/-- Every integral-unit reflection preserves every fixed-value integral shell. -/
theorem integralReflect_mem_shell (L : Submodule (𝓞 K) V)
    (B : BilinForm K V) (hB : B.IsSymm)
    (hQ : ∀ x ∈ L, IsIntegral ℤ (B x x))
    (u : (𝓞 K)ˣ) (e : K) {v x : V}
    (hv : v ∈ L ∧ B v v = ((u : 𝓞 K) : K))
    (hx : x ∈ L ∧ B x x = e) :
    integralReflect B v x ∈ L ∧
      B (integralReflect B v x) (integralReflect B v x) = e := by
  refine ⟨integralReflect_mem L B hB hQ hv.1 hx.1 u hv.2, ?_⟩
  rw [integralReflect_norm B hB v x, hx.2]
  rw [hv.2]
  exact (RingOfIntegers.coe_ne_zero_iff (K := K)).2 u.ne_zero

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/-- Collinear represented units have equal squareclasses in the actual integer unit group. -/
theorem collinear_unit_values_same_squareclass
    (B : BilinForm K V) (u v : (𝓞 K)ˣ) (x y : V)
    (hx : B x x = ((u : 𝓞 K) : K))
    (hy : B y y = ((v : 𝓞 K) : K))
    (c : K) (hc : y = c • x) :
    ∃ w : (𝓞 K)ˣ, v = w ^ 2 * u := by
  apply exists_integral_unit_of_ratio_sq u v c
  rw [← hy, hc, BilinForm.smul_left, BilinForm.smul_right, hx]
  ring

end Lattice

end UnitSquareclass

#print axioms UnitSquareclass.exists_integral_unit_of_ratio_sq
#print axioms UnitSquareclass.two_mul_bilin_isIntegral
#print axioms UnitSquareclass.integralReflect_mem_shell
#print axioms UnitSquareclass.collinear_unit_values_same_squareclass

