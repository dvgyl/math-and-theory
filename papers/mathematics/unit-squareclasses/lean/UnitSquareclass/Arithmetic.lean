import Mathlib

/-! Arithmetic lemmas for represented unit squareclasses.
This file is work in progress until every endpoint is built and audited.
-/

noncomputable section
open scoped BigOperators
namespace UnitSquareclass

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma bilinear_det_identity (B : LinearMap.BilinForm K V) (hs : B.IsSymm)
    (x y : V) :
    B ((B y y) • x - (B x y) • y) ((B y y) • x - (B x y) • y) =
      (B y y) * ((B x x) * (B y y) - (B x y)^2) := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show B y x = B x y from hs y x]
  ring

lemma mapped_cauchy (B : LinearMap.BilinForm K V) (hs : B.IsSymm)
    (φ : K →+* ℝ) (hp : ∀ v : V, 0 ≤ φ (B v v))
    (x y : V) (hy : 0 < φ (B y y)) :
    (φ (B x y))^2 ≤ φ (B x x) * φ (B y y) := by
  have h := hp ((B y y) • x - (B x y) • y)
  rw [bilinear_det_identity B hs x y, map_mul, map_sub, map_mul, map_pow] at h
  have hd : 0 ≤ φ (B x x) * φ (B y y) - φ (B x y)^2 :=
    (mul_nonneg_iff_of_pos_left hy).mp h
  linarith

def realEmbeddingOfRealImage (φ : K →+* ℂ)
    (hr : ∀ x : K, (φ x).im = 0) : K →+* ℝ where
  toFun x := (φ x).re
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp [Complex.mul_re, hr]

lemma norm_embedding_eq_abs_re (φ : K →+* ℂ)
    (hr : ∀ x : K, (φ x).im = 0) (x : K) :
    ‖φ x‖ = |(φ x).re| := by
  exact (Complex.abs_re_eq_norm.mpr (hr x)).symm

section ArithmeticFiniteness
variable [NumberField K] {J : Type*} [Fintype J]

lemma finite_of_bounded_integral_coordinates
    (S : Set V) (g : V → J → K) (hg : Set.InjOn g S) (C : J → ℝ)
    (hb : ∀ x ∈ S, ∀ j,
      IsIntegral ℤ (g x j) ∧ ∀ φ : K →+* ℂ, ‖φ (g x j)‖ ≤ C j) :
    S.Finite := by
  classical
  let T : J → Set K := fun j =>
    {a : K | IsIntegral ℤ a ∧ ∀ φ : K →+* ℂ, ‖φ a‖ ≤ C j}
  have hf : (Set.univ.pi T).Finite := Set.Finite.pi fun j =>
    NumberField.Embeddings.finite_of_norm_le K ℂ (C j)
  have hi : g '' S ⊆ Set.univ.pi T := by
    rintro _ ⟨x, hx, rfl⟩ j _
    exact hb x hx j
  exact (hf.subset hi).of_finite_image hg

lemma polar_coordinates_injective
    (B : LinearMap.BilinForm K V)
    (ha : ∀ v : V, B v v = 0 → v = 0) (e : J → V) :
    Set.InjOn (fun x : V => fun j => (2 : K) * B x (e j))
      (Submodule.span K (Set.range e) : Set V) := by
  intro x hx y hy heq
  have hz : x - y ∈ Submodule.span K (Set.range e) :=
    (Submodule.span K (Set.range e)).sub_mem hx hy
  have ho : ∀ j, B (x-y) (e j) = 0 := by
    intro j
    have hj := congrFun heq j
    have hc : B x (e j) = B y (e j) :=
      mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) hj
    simp [map_sub, LinearMap.sub_apply, hc]
  have hw : ∀ w ∈ Submodule.span K (Set.range e), B (x-y) w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz => obtain ⟨j, rfl⟩ := hz; exact ho j
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul a b _ hb => simp only [map_smul, hb, smul_zero]
  exact sub_eq_zero.mp (ha (x-y) (hw (x-y) hz))

lemma mapped_polar_norm_bound (B : LinearMap.BilinForm K V) (hs : B.IsSymm)
    (φ : K →+* ℂ) (hr : ∀ a : K, (φ a).im = 0)
    (hp : ∀ v : V, v ≠ 0 → 0 < (φ (B v v)).re)
    (x y : V) :
    ‖φ (2 * B x y)‖ ≤ 1 + 4 * ‖φ (B x x)‖ * ‖φ (B y y)‖ := by
  let ψ := realEmbeddingOfRealImage φ hr
  have hp' : ∀ v : V, 0 ≤ ψ (B v v) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact le_of_lt (hp v hv)
  by_cases hy : y = 0
  · simp [hy]
  have hyy : 0 < ψ (B y y) := hp y hy
  have hc := mapped_cauchy B hs ψ hp' x y hyy
  rw [norm_embedding_eq_abs_re φ hr, norm_embedding_eq_abs_re φ hr,
    norm_embedding_eq_abs_re φ hr]
  change |ψ (2 * B x y)| ≤ 1 + 4 * |ψ (B x x)| * |ψ (B y y)|
  rw [map_mul, map_ofNat, abs_of_nonneg (hp' x), abs_of_nonneg (hp' y)]
  have ha := abs_nonneg (2 * ψ (B x y))
  have hab := sq_abs (2 * ψ (B x y))
  have ht := sq_nonneg (|2 * ψ (B x y)| - 1)
  have hx := hp' x
  have hy' := hp' y
  nlinarith

/-- Arithmetic shell finiteness from a finite spanning family and integral polar coordinates.
The bound is derived from all embeddings of the number field, not assumed as a shell axiom. -/
theorem finite_arithmetic_shell
    (B : LinearMap.BilinForm K V) (hs : B.IsSymm)
    (ha : ∀ v : V, B v v = 0 → v = 0)
    (hr : ∀ (φ : K →+* ℂ) (a : K), (φ a).im = 0)
    (hp : ∀ (φ : K →+* ℂ) (v : V), v ≠ 0 → 0 < (φ (B v v)).re)
    (M : Set V) (e : J → V)
    (hspan : ∀ x ∈ M, x ∈ Submodule.span K (Set.range e))
    (hi : ∀ x ∈ M, ∀ j, IsIntegral ℤ ((2 : K) * B x (e j)))
    (ε : K) :
    {x : V | x ∈ M ∧ B x x = ε}.Finite := by
  classical
  let S : Set V := {x : V | x ∈ M ∧ B x x = ε}
  let g : V → J → K := fun x j => 2 * B x (e j)
  let C : J → ℝ := fun j => 1 + 4 *
    (∑ φ : K →+* ℂ, ‖φ ε‖) * (∑ φ : K →+* ℂ, ‖φ (B (e j) (e j))‖)
  have hinj : Set.InjOn g S :=
    (polar_coordinates_injective B ha e).mono (fun x hx => hspan x hx.1)
  apply finite_of_bounded_integral_coordinates S g hinj C
  intro x hx j
  refine ⟨hi x hx.1 j, ?_⟩
  intro φ
  have h := mapped_polar_norm_bound B hs φ (hr φ) (hp φ) x (e j)
  rw [hx.2] at h
  have hε : ‖φ ε‖ ≤ ∑ ψ : K →+* ℂ, ‖ψ ε‖ :=
    Finset.single_le_sum (fun ψ _ => norm_nonneg (ψ ε)) (Finset.mem_univ φ)
  have he : ‖φ (B (e j) (e j))‖ ≤ ∑ ψ : K →+* ℂ, ‖ψ (B (e j) (e j))‖ :=
    Finset.single_le_sum (fun ψ _ => norm_nonneg (ψ (B (e j) (e j)))) (Finset.mem_univ φ)
  apply h.trans
  dsimp [C]
  gcongr

end ArithmeticFiniteness

end UnitSquareclass
