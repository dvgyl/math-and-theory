module

public import MatCKronecker.BlockSum
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

namespace MatCKronecker

open Matrix Module

variable {m n p q : Type*} [Fintype n] [Fintype q]

/-- Ordinary matrix rank is additive on an actual rectangular block diagonal,
including empty row and column types. -/
theorem rank_fromBlocks (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let eo := LinearEquiv.sumArrowLequivProdArrow m p ℝ ℝ
  let ei := LinearEquiv.sumArrowLequivProdArrow n q ℝ ℝ
  let D := Matrix.fromBlocks A 0 0 B
  have hcomm : eo.toLinearMap.comp D.mulVecLin =
      (A.mulVecLin.prodMap B.mulVecLin).comp ei.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i
      change (D *ᵥ x) (Sum.inl i) = (A *ᵥ (x ∘ Sum.inl)) i
      simp [D, Matrix.fromBlocks_mulVec]
    · funext i
      change (D *ᵥ x) (Sum.inr i) = (B *ᵥ (x ∘ Sum.inr)) i
      simp [D, Matrix.fromBlocks_mulVec]
  have hmap : D.mulVecLin.range.map eo.toLinearMap =
      A.mulVecLin.range.prod B.mulVecLin.range := by
    rw [← LinearMap.range_comp, hcomm,
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top_of_surjective _ ei.surjective), LinearMap.range_prodMap]
  change finrank ℝ D.mulVecLin.range = _
  calc
    finrank ℝ D.mulVecLin.range =
        finrank ℝ (D.mulVecLin.range.map eo.toLinearMap) :=
      (eo.finrank_map_eq D.mulVecLin.range).symm
    _ = finrank ℝ (A.mulVecLin.range.prod B.mulVecLin.range) := by rw [hmap]
    _ = finrank ℝ (A.mulVecLin.range × B.mulVecLin.range) :=
      (Submodule.prodEquiv _ _).finrank_eq
    _ = A.rank + B.rank := by rw [Module.finrank_prod]; rfl

end MatCKronecker
