module

public import PositiveCore.NullspaceAbsorption
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

namespace PositiveCore

open Matrix Module

section LinearMaps

variable {E F G D : Type*}
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]
  [AddCommGroup D] [Module ℝ D] [FiniteDimensional ℝ D]

/-- The available directions are the image of the left kernel in the quotient
by the range of the right factor. -/
def capacityMap (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] E) :
    LinearMap.ker f →ₗ[ℝ] E ⧸ LinearMap.range g :=
  (LinearMap.range g).mkQ.comp (LinearMap.ker f).subtype

theorem finrank_comap_subtype (S T : Submodule ℝ E) :
    finrank ℝ (T.comap S.subtype) = finrank ℝ (S ⊓ T : Submodule ℝ E) := by
  have h := (S.equivSubtypeMap (T.comap S.subtype)).finrank_eq
  rw [Submodule.map_comap_subtype] at h
  exact h

/-- Exact dimension of the usable paired nullspace.  The addition-only identity
avoids any convention about truncated natural subtraction. -/
theorem capacity_dimension (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] E) :
    finrank ℝ (LinearMap.range (capacityMap f g)) +
      finrank ℝ (LinearMap.range f) + finrank ℝ (LinearMap.range g) =
    finrank ℝ E + finrank ℝ (LinearMap.range (f.comp g)) := by
  let h := capacityMap f g
  have hh := h.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hg := (f.domRestrict (LinearMap.range g)).finrank_range_add_finrank_ker
  have hker : finrank ℝ (LinearMap.ker h) =
      finrank ℝ (LinearMap.ker (f.domRestrict (LinearMap.range g))) := by
    change finrank ℝ (LinearMap.ker ((LinearMap.range g).mkQ.comp
      (LinearMap.ker f).subtype)) = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, LinearMap.ker_domRestrict,
      finrank_comap_subtype, finrank_comap_subtype, inf_comm]
  have hrange : LinearMap.range (f.domRestrict (LinearMap.range g)) =
      LinearMap.range (f.comp g) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  rw [hrange] at hg
  change finrank ℝ (LinearMap.range h) + finrank ℝ (LinearMap.range f) +
    finrank ℝ (LinearMap.range g) = _
  omega

/-- Exact existence criterion for a pair of annihilating maps with identity
pairing.  This is valid for every real finite-dimensional latent space. -/
theorem exists_nullspace_frame_iff_dimension
    (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] E) :
    (∃ z : D →ₗ[ℝ] E, ∃ w : E →ₗ[ℝ] D,
      f.comp z = 0 ∧ w.comp g = 0 ∧ w.comp z = LinearMap.id) ↔
      finrank ℝ D ≤ finrank ℝ (LinearMap.range (capacityMap f g)) := by
  classical
  let h := capacityMap f g
  constructor
  · rintro ⟨z, w, hfz, hwg, hwz⟩
    let zK : D →ₗ[ℝ] LinearMap.ker f := z.codRestrict _ (fun x => by
      change f (z x) = 0
      exact LinearMap.congr_fun hfz x)
    let wQ : (E ⧸ LinearMap.range g) →ₗ[ℝ] D :=
      (LinearMap.range g).liftQ w (LinearMap.range_le_ker_iff.mpr hwg)
    let a := h.comp zK
    have hwa : wQ.comp a = LinearMap.id := by
      ext x
      change w (z x) = x
      exact LinearMap.congr_fun hwz x
    have hinj : Function.Injective a :=
      LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot_of_inverse hwa)
    have hdim := LinearMap.finrank_range_of_inj hinj
    have hle : LinearMap.range a ≤ LinearMap.range h :=
      LinearMap.range_comp_le_range zK h
    change finrank ℝ D ≤ finrank ℝ (LinearMap.range h)
    rw [← hdim]
    exact Submodule.finrank_mono hle
  · intro hdim
    change finrank ℝ D ≤ finrank ℝ (LinearMap.range h) at hdim
    obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hdim
    let i : D →ₗ[ℝ] E ⧸ LinearMap.range g := (LinearMap.range h).subtype.comp e
    have hi : Function.Injective i :=
      (LinearMap.range h).subtype_injective.comp he
    obtain ⟨wQ, hwQ⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
    obtain ⟨s, hs⟩ := h.rangeRestrict.exists_rightInverse_of_surjective h.range_rangeRestrict
    let zK : D →ₗ[ℝ] LinearMap.ker f := s.comp e
    let z : D →ₗ[ℝ] E := (LinearMap.ker f).subtype.comp zK
    let w : E →ₗ[ℝ] D := wQ.comp (LinearMap.range g).mkQ
    refine ⟨z, w, ?_, ?_, ?_⟩
    · ext x
      exact (zK x).property
    · ext x
      change wQ ((LinearMap.range g).mkQ (g x)) = 0
      have hgx : (LinearMap.range g).mkQ (g x) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [Submodule.ker_mkQ]
        exact LinearMap.mem_range_self g x
      rw [hgx, map_zero]
    · ext x
      have hsx := LinearMap.congr_fun hs (e x)
      have hsx' := congrArg (fun a : LinearMap.range h => (a : E ⧸ LinearMap.range g)) hsx
      have hi_eq : (LinearMap.range g).mkQ (z x) = i x := by
        exact hsx'
      change wQ ((LinearMap.range g).mkQ (z x)) = x
      rw [hi_eq]
      exact LinearMap.congr_fun hwQ x

/-- Rank form of the exact capacity criterion. -/
theorem exists_nullspace_frame_iff
    (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] E) :
    (∃ z : D →ₗ[ℝ] E, ∃ w : E →ₗ[ℝ] D,
      f.comp z = 0 ∧ w.comp g = 0 ∧ w.comp z = LinearMap.id) ↔
      finrank ℝ D + finrank ℝ (LinearMap.range f) + finrank ℝ (LinearMap.range g) ≤
        finrank ℝ E + finrank ℝ (LinearMap.range (f.comp g)) := by
  rw [exists_nullspace_frame_iff_dimension]
  have hd := capacity_dimension f g
  omega

end LinearMaps

section Matrices

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq p] [DecidableEq q]

/-- The maximal paired nullspace width is exactly
`card p + rank (U V) - rank U - rank V`.  The addition-only formulation handles
all zero-dimensional cases without truncated subtraction. -/
theorem exists_matrix_nullspace_frame_iff
    (U : Matrix m p ℝ) (V : Matrix p n ℝ) :
    (∃ Z : Matrix p q ℝ, ∃ W : Matrix q p ℝ,
      U * Z = 0 ∧ W * V = 0 ∧ W * Z = 1) ↔
      Fintype.card q + U.rank + V.rank ≤ Fintype.card p + (U * V).rank := by
  classical
  have h := exists_nullspace_frame_iff (D := q → ℝ) U.mulVecLin V.mulVecLin
  simp only [finrank_pi, Matrix.rank] at h ⊢
  rw [Matrix.mulVecLin_mul]
  rw [← h]
  constructor
  · rintro ⟨Z, W, hUZ, hWV, hWZ⟩
    refine ⟨Z.mulVecLin, W.mulVecLin, ?_, ?_, ?_⟩
    · rw [← Matrix.mulVecLin_mul, hUZ, Matrix.mulVecLin_zero]
    · rw [← Matrix.mulVecLin_mul, hWV, Matrix.mulVecLin_zero]
    · rw [← Matrix.mulVecLin_mul, hWZ, Matrix.mulVecLin_one]
  · rintro ⟨z, w, hfz, hwg, hwz⟩
    refine ⟨LinearMap.toMatrix' z, LinearMap.toMatrix' w, ?_, ?_, ?_⟩
    · apply Matrix.toLin'.injective
      change (U * LinearMap.toMatrix' z).mulVecLin = (0 : Matrix m q ℝ).mulVecLin
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_zero]
      change U.mulVecLin.comp (Matrix.toLin' (LinearMap.toMatrix' z)) = 0
      rw [Matrix.toLin'_toMatrix']
      exact hfz
    · apply Matrix.toLin'.injective
      change (LinearMap.toMatrix' w * V).mulVecLin = (0 : Matrix q n ℝ).mulVecLin
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_zero]
      change (Matrix.toLin' (LinearMap.toMatrix' w)).comp V.mulVecLin = 0
      rw [Matrix.toLin'_toMatrix']
      exact hwg
    · apply Matrix.toLin'.injective
      change (LinearMap.toMatrix' w * LinearMap.toMatrix' z).mulVecLin =
        (1 : Matrix q q ℝ).mulVecLin
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one]
      change (Matrix.toLin' (LinearMap.toMatrix' w)).comp
        (Matrix.toLin' (LinearMap.toMatrix' z)) = LinearMap.id
      rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
      exact hwz

end Matrices

end PositiveCore
