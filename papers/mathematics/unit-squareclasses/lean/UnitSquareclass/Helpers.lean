import Mathlib

/-! Transport the existing field operations to the ordering defined by a real embedding. -/

namespace UnitSquareclass

variable {K : Type*} [Field K]

noncomputable def realEmbeddingLinearOrder (φ : K →+* ℝ) : LinearOrder K :=
  LinearOrder.lift' φ φ.injective

theorem realEmbeddingStrictOrderedRing (φ : K →+* ℝ) :
    letI : LinearOrder K := realEmbeddingLinearOrder φ
    IsStrictOrderedRing K := by
  letI : LinearOrder K := realEmbeddingLinearOrder φ
  exact φ.injective.isStrictOrderedRing φ φ.map_zero φ.map_one
    φ.map_add φ.map_mul (fun n x => map_nsmul φ n x)
    (fun x n => map_pow φ x n) (fun n => map_natCast φ n)

end UnitSquareclass

#print axioms UnitSquareclass.realEmbeddingStrictOrderedRing
