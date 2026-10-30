import CoreDefs
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
The tensor-subspace theorem formalized below is an existing result:
Chen, Yang, and Tang, arXiv:1609.05100, Lemma 19(i), published in
Quantum Information Processing (2017). It is used as a verified ingredient
of the candidate cone application, not claimed as a new research theorem.
-/

namespace PPTCone

open LinearMap
open scoped BigOperators Matrix

/-- A finite-dimensional complex matrix pencil with nested images
has a nonzero value on which its two members are proportional. -/
theorem pencil_has_dependent_value
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f g : V →ₗ[ℂ] W) (hf : f ≠ 0)
    (hrange : LinearMap.range g ≤ LinearMap.range f) :
    ∃ x : V, ∃ c : ℂ, f x ≠ 0 ∧ g x = c • f x := by
  classical
  let R := LinearMap.range f
  let fr : V →ₗ[ℂ] R := f.rangeRestrict
  let gr : V →ₗ[ℂ] R := g.codRestrict R (fun x => hrange (LinearMap.mem_range_self g x))
  obtain ⟨s, hs⟩ := fr.exists_rightInverse_of_surjective f.range_rangeRestrict
  have hnon : Nontrivial R := by
    have hfx : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hfx
    exact ⟨⟨⟨f x, LinearMap.mem_range_self f x⟩, 0,
      fun h => hx (congrArg Subtype.val h)⟩⟩
  letI := hnon
  let e : Module.End ℂ R := gr.comp s
  obtain ⟨c, hc⟩ := e.exists_eigenvalue
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨s v, c, ?_, ?_⟩
  · have hfs : fr (s v) = v := by
      simpa using LinearMap.congr_fun hs v
    intro hz
    apply hv.2
    apply Subtype.ext
    change (v : W) = 0
    rw [← hfs]
    exact hz
  · have hev := hv.apply_eq_smul
    have hfs : fr (s v) = v := by
      simpa using LinearMap.congr_fun hs v
    change g (s v) = c • f (s v)
    have h := congrArg Subtype.val hev
    change g (s v) = c • (v : W) at h
    exact h.trans (congrArg (fun w : W => c • w)
      (congrArg Subtype.val hfs).symm)

theorem dual_apply_eq_sum {A : Type*} [Fintype A] [DecidableEq A]
    (φ : Module.Dual ℂ (A → ℂ)) (z : A → ℂ) :
    φ z = ∑ i, φ (Pi.single i 1) * z i := by
  have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : A → ℂ) := by
    ext j
    simp [Pi.single_apply]
  calc
    φ z = φ (∑ i, z i • (Pi.single i (1 : ℂ) : A → ℂ)) := congrArg φ hz
    _ = ∑ i, φ (Pi.single i 1) * z i := by
      simp [map_sum, map_smul, mul_comm]

theorem noProduct_factor_right {A B : Type*}
    (S : Submodule ℂ (Matrix A B ℂ)) (hS : NoProduct S)
    (u : A → ℂ) (v : B → ℂ) (hu : u ≠ 0)
    (h : (fun i j => u i * v j) ∈ S) : v = 0 := by
  have hz := hS u v h
  have hu' : ∃ i, u i ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hu (funext hh)
  obtain ⟨i, hi⟩ := hu'
  ext j
  have hij := congrFun (congrFun hz i) j
  exact (mul_eq_zero.mp hij).resolve_left hi

theorem noProduct_factor_left {A B : Type*}
    (S : Submodule ℂ (Matrix A B ℂ)) (hS : NoProduct S)
    (u : A → ℂ) (v : B → ℂ) (hv : v ≠ 0)
    (h : (fun i j => u i * v j) ∈ S) : u = 0 := by
  have hz := hS u v h
  have hv' : ∃ j, v j ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hv (funext hh)
  obtain ⟨j, hj⟩ := hv'
  ext i
  have hij := congrFun (congrFun hz i) j
  exact (mul_eq_zero.mp hij).resolve_right hj

theorem contract_column_mem
    {A B C D : Type*} [Fintype C]
    (S : Submodule ℂ (Matrix A B ℂ))
    (U₀ U₁ : Matrix A C ℂ) (V₀ V₁ : Matrix B D ℂ)
    (hS : ∀ c d, (fun a b => U₀ a c * V₀ b d + U₁ a c * V₁ b d) ∈ S)
    (x : C → ℂ) (d : D) :
    (fun a b => (U₀ *ᵥ x) a * V₀ b d + (U₁ *ᵥ x) a * V₁ b d) ∈ S := by
  have hm := S.sum_mem (fun c (_ : c ∈ Finset.univ) => S.smul_mem (x c) (hS c d))
  convert hm using 1
  ext a b
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem contract_row_mem
    {A B C D : Type*} [Fintype A] [DecidableEq A]
    (T : Submodule ℂ (Matrix C D ℂ))
    (U₀ U₁ : Matrix A C ℂ) (V₀ V₁ : Matrix B D ℂ)
    (hT : ∀ a b, (fun c d => U₀ a c * V₀ b d + U₁ a c * V₁ b d) ∈ T)
    (φ : Module.Dual ℂ (A → ℂ)) (b : B) :
    (fun c d => φ (fun a => U₀ a c) * V₀ b d +
      φ (fun a => U₁ a c) * V₁ b d) ∈ T := by
  have hm := T.sum_mem (fun a (_ : a ∈ Finset.univ) =>
    T.smul_mem (φ (Pi.single a 1)) (hT a b))
  convert hm using 1
  ext c d
  rw [dual_apply_eq_sum φ (fun a => U₀ a c),
    dual_apply_eq_sum φ (fun a => U₁ a c)]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem mulVec_eq_sum_columns {A C : Type*} [Fintype C]
    (U : Matrix A C ℂ) (x : C → ℂ) :
    U *ᵥ x = ∑ c, x c • (fun a => U a c) := by
  ext a
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- The rank-two part of the CES tensor-product theorem, written in matrix
coordinates. Each assumption is a genuine slice-membership condition. -/
theorem rank_two_slices_zero
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (S : Submodule ℂ (Matrix A B ℂ)) (T : Submodule ℂ (Matrix C D ℂ))
    (hS : NoProduct S) (hT : NoProduct T)
    (U₀ U₁ : Matrix A C ℂ) (V₀ V₁ : Matrix B D ℂ)
    (hSC : ∀ c d, (fun a b => U₀ a c * V₀ b d + U₁ a c * V₁ b d) ∈ S)
    (hTC : ∀ a b, (fun c d => U₀ a c * V₀ b d + U₁ a c * V₁ b d) ∈ T) :
    ∀ a c b d, U₀ a c * V₀ b d + U₁ a c * V₁ b d = 0 := by
  classical
  by_cases hU : U₀ = 0
  · subst U₀
    intro a c b d
    have hm : (fun a b => U₁ a c * V₁ b d) ∈ S := by
      simpa using hSC c d
    have hz := hS (fun a => U₁ a c) (fun b => V₁ b d) hm
    simpa using congrFun (congrFun hz a) b
  by_cases hV : V₁ = 0
  · subst V₁
    intro a c b d
    have hm : (fun a b => U₀ a c * V₀ b d) ∈ S := by
      simpa using hSC c d
    have hz := hS (fun a => U₀ a c) (fun b => V₀ b d) hm
    simpa using congrFun (congrFun hz a) b
  let f := U₀.mulVecLin
  let g := U₁.mulVecLin
  have hf : f ≠ 0 := by
    intro hz
    apply hU
    ext a c
    have hcol := LinearMap.congr_fun hz (Pi.single c 1)
    have hcol' : (fun a => U₀ a c) = 0 := by
      simpa [f, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hcol
    exact congrFun hcol' a
  have hrowV : ∃ b, V₁ b ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hV (funext hh)
  obtain ⟨b₀, hb₀⟩ := hrowV
  have hrange : LinearMap.range g ≤ LinearMap.range f := by
    rintro y ⟨x, rfl⟩
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range f) (g x)).mp
    intro φ hφ
    have hφf : ∀ z, φ (f z) = 0 := by
      intro z
      exact ((Submodule.mem_dualAnnihilator φ).mp hφ) (f z) (LinearMap.mem_range_self f z)
    have hφcol : ∀ c, φ (fun a => U₀ a c) = 0 := by
      intro c
      simpa [f, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hφf (Pi.single c 1)
    have hm : (fun c d => φ (fun a => U₁ a c) * V₁ b₀ d) ∈ T := by
      simpa only [hφcol, zero_mul, zero_add] using
        contract_row_mem T U₀ U₁ V₀ V₁ hTC φ b₀
    have hz := noProduct_factor_left T hT (fun c => φ (fun a => U₁ a c))
      (V₁ b₀) hb₀ hm
    change φ (U₁ *ᵥ x) = 0
    rw [mulVec_eq_sum_columns, map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [map_smul]
    have hc : φ (fun a => U₁ a c) = 0 := congrFun hz c
    simp [hc]
  obtain ⟨x, z, hfx, hgx⟩ := pencil_has_dependent_value f g hf hrange
  have hrel : ∀ b d, V₀ b d + z * V₁ b d = 0 := by
    intro b d
    have hm : (fun a b => (f x) a * (V₀ b d + z * V₁ b d)) ∈ S := by
      convert contract_column_mem S U₀ U₁ V₀ V₁ hSC x d using 1
      ext a b
      change (f x) a * (V₀ b d + z * V₁ b d) =
        (f x) a * V₀ b d + (g x) a * V₁ b d
      rw [hgx]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hz := noProduct_factor_right S hS (f x)
      (fun b => V₀ b d + z * V₁ b d) hfx hm
    exact congrFun hz b
  intro a c b d
  have hm : (fun a b => (U₁ a c - z * U₀ a c) * V₁ b d) ∈ S := by
    convert hSC c d using 1
    ext a b
    linear_combination -(U₀ a c) * hrel b d
  have hz := hS (fun a => U₁ a c - z * U₀ a c) (fun b => V₁ b d) hm
  have he := congrFun (congrFun hz a) b
  change (U₁ a c - z * U₀ a c) * V₁ b d = 0 at he
  linear_combination he + (U₀ a c) * hrel b d

/-- Tensor products of two completely entangled matrix subspaces contain no
nonzero vector of Schmidt rank at most two across the regrouped bipartition.
The two slice conditions express membership in the tensor-product subspace. -/
theorem tensor_no_sr2
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (S : Submodule ℂ (Matrix A B ℂ)) (T : Submodule ℂ (Matrix C D ℂ))
    (hS : NoProduct S) (hT : NoProduct T)
    (v : (A × C) × (B × D) → ℂ)
    (hslices : ∀ c d, (fun a b => v ((a,c),(b,d))) ∈ S)
    (htslices : ∀ a b, (fun c d => v ((a,c),(b,d))) ∈ T)
    (hv : HasSR2 v) : v = 0 := by
  obtain ⟨u₀, u₁, v₀, v₁, hv⟩ := hv
  have hz := rank_two_slices_zero S T hS hT
    (fun a c => u₀ (a,c)) (fun a c => u₁ (a,c))
    (fun b d => v₀ (b,d)) (fun b d => v₁ (b,d))
    (fun c d => by simpa only [hv] using hslices c d)
    (fun a b => by simpa only [hv] using htslices a b)
  ext p
  rcases p with ⟨⟨a,c⟩,⟨b,d⟩⟩
  simpa only [hv] using hz a c b d

end PPTCone
