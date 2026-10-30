import CoreDefs
import Mathlib.Data.Matrix.Rank

open scoped Matrix BigOperators

namespace PPTCone

theorem rank_select_columns_le
    {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    (X : Matrix A B ℂ) (f : D → B) :
    (X.submatrix id f).rank ≤ X.rank := by
  classical
  have h := Matrix.rank_mul_le_left X ((1 : Matrix B B ℂ).submatrix (Equiv.refl B) f)
  rw [Matrix.mul_submatrix_one (Equiv.refl B) f X] at h
  simpa only [Equiv.refl_symm, Equiv.coe_refl,
    Function.id_comp] using h

theorem rank_select_rows_le
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (X : Matrix A B ℂ) (f : C → A) :
    (X.submatrix f id).rank ≤ X.rank := by
  classical
  have h := Matrix.rank_mul_le_right ((1 : Matrix A A ℂ).submatrix f (Equiv.refl A)) X
  rw [Matrix.one_submatrix_mul f (Equiv.refl A) X] at h
  simpa only [Equiv.refl_symm, Equiv.coe_refl,
    Function.id_comp] using h

/-- If the middle composition vanishes, the two compressed ranks fit
disjointly inside the rank of the original matrix. -/
theorem rank_compressions_add_le
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (X : Matrix A B ℂ) (P : Matrix C A ℂ) (Q : Matrix B D ℂ)
    (h : P * X * Q = 0) :
    (P * X).rank + (X * Q).rank ≤ X.rank := by
  classical
  let W := LinearMap.range X.mulVecLin
  let g : W →ₗ[ℂ] (C → ℂ) := P.mulVecLin.comp W.subtype
  have hgrange : LinearMap.range g = LinearMap.range (P * X).mulVecLin := by
    simp [g, W, Matrix.mulVecLin_mul, LinearMap.range_comp]
  have hyW : ∀ y : LinearMap.range (X * Q).mulVecLin, (y : A → ℂ) ∈ W := by
    rintro ⟨y, z, hz⟩
    refine ⟨Q *ᵥ z, ?_⟩
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using hz
  have hyg : ∀ y : LinearMap.range (X * Q).mulVecLin,
      g ⟨(y : A → ℂ), hyW y⟩ = 0 := by
    rintro ⟨y, z, hz⟩
    change P *ᵥ y = 0
    rw [← hz]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, h]
    simp
  let j : LinearMap.range (X * Q).mulVecLin →ₗ[ℂ] LinearMap.ker g :=
    { toFun := fun y => ⟨⟨(y : A → ℂ), hyW y⟩, hyg y⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hj : Function.Injective j := by
    intro x y hh
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker g => ((z : W) : A → ℂ)) hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hj
  have hdimW := g.finrank_range_add_finrank_ker
  rw [hgrange] at hdimW
  change (P * X).rank + Module.finrank ℂ (LinearMap.ker g) = X.rank at hdimW
  exact (Nat.add_le_add_left hdim _).trans_eq hdimW

end PPTCone
