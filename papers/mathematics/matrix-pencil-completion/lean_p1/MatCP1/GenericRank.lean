module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Polynomial.Roots

public section

open Filter

namespace MatCP1

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

theorem eventually_bijective_affine [FiniteDimensional F V]
    (f g : V →ₗ[F] V) (a : F) (ha : Function.Bijective (f + a • g)) :
    ∀ᶠ z : F in Filter.cofinite, Function.Bijective (f + z • g) := by
  classical
  let b := Module.finBasis F V
  let M := LinearMap.toMatrix b b f
  let N := LinearMap.toMatrix b b g
  let P : Matrix (Fin (Module.finrank F V)) (Fin (Module.finrank F V)) (Polynomial F) :=
    fun i j => Polynomial.C (M i j) + Polynomial.X * Polynomial.C (N i j)
  have hev (z : F) : P.det.eval z = (f + z • g).det := by
    rw [← LinearMap.det_toMatrix b]
    change (Polynomial.evalRingHom z) P.det = _
    rw [(Polynomial.evalRingHom z).map_det]
    congr 1
    ext i j
    change (Polynomial.evalRingHom z) (P i j) = LinearMap.toMatrix b b (f + z • g) i j
    simp [P, M, N]
    exact mul_comm _ _
  have hp : P.det ≠ 0 := by
    intro h
    have hz : (f + a • g).det = 0 := by rw [← hev, h]; simp
    have hk := (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz)
    exact hk (LinearMap.ker_eq_bot.mpr ha.injective)
  filter_upwards [Polynomial.eventually_eval_ne_zero_cofinite hp] with z hz
  have hd : (f + z • g).det ≠ 0 := by simpa [hev] using hz
  have hi : Function.Injective (f + z • g) := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hk
    exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  exact ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩

theorem eventually_injective_affine [FiniteDimensional F V]
    (f g : V →ₗ[F] W) (a : F) (ha : Function.Injective (f + a • g)) :
    ∀ᶠ z : F in Filter.cofinite, Function.Injective (f + z • g) := by
  obtain ⟨l, hl⟩ := (f + a • g).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ha)
  have hla : l.comp f + a • l.comp g = LinearMap.id := by
    simpa only [LinearMap.comp_add, LinearMap.comp_smul] using hl
  have hbij : Function.Bijective (l.comp f + a • l.comp g) := by
    rw [hla]
    exact Function.bijective_id
  filter_upwards [eventually_bijective_affine (l.comp f) (l.comp g) a hbij]
    with z hz
  intro x y hxy
  apply hz.injective
  simpa using congrArg l hxy

theorem eventually_surjective_affine [FiniteDimensional F W]
    (f g : V →ₗ[F] W) (a : F) (ha : Function.Surjective (f + a • g)) :
    ∀ᶠ z : F in Filter.cofinite, Function.Surjective (f + z • g) := by
  obtain ⟨r, hr⟩ := (f + a • g).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr ha)
  have hra : f.comp r + a • g.comp r = LinearMap.id := by
    simpa only [LinearMap.add_comp, LinearMap.smul_comp] using hr
  have hbij : Function.Bijective (f.comp r + a • g.comp r) := by
    rw [hra]
    exact Function.bijective_id
  filter_upwards [eventually_bijective_affine (f.comp r) (g.comp r) a hbij]
    with z hz
  intro y
  obtain ⟨x, hx⟩ := hz.surjective y
  exact ⟨r x, by simpa using hx⟩

end MatCP1
