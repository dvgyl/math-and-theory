import TilesBase
import GeneralDefs

open scoped BigOperators Matrix

namespace PPTCone

/-- The five Tiles constraints as the bilinear product contractions used in
matrix-rank arguments. The coefficients are real, so they also equal the
Hermitian inner products with the five actual product vectors. -/
theorem tiles_bilinear_eq_constraint (X : M3) (t : Fin 5) :
    (∑ a : Fin 3, ∑ b : Fin 3, tilesLeft t a * X a b * tilesRight t b) =
      tilesConstraints X t := by
  calc
    _ = dotProduct (tilesVector t) (Function.uncurry X) := by
      simp only [dotProduct, tilesVector, Fintype.sum_prod_type, Function.uncurry_apply_pair]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := tilesVector_dot_eq (Function.uncurry X) t

theorem tilesSpace_bilinear_iff (X : M3) : X ∈ tilesSpace ↔
    ∀ t : Fin 5, (∑ a : Fin 3, ∑ b : Fin 3,
      tilesLeft t a * X a b * tilesRight t b) = 0 := by
  constructor
  · intro h t
    have hc : tilesConstraints X = 0 := h
    rw [tiles_bilinear_eq_constraint, hc]
    rfl
  · intro h
    change tilesConstraints X = 0
    ext t
    simpa only [tiles_bilinear_eq_constraint] using h t

/-- Actual unextendibility of the five Tiles product vectors, in bilinear
coordinates; no mutual-orthogonality assumption is needed by this API. -/
theorem tiles_unextendible (u v : Fin 3 → ℂ)
    (h : ∀ t : Fin 5, (∑ a : Fin 3, tilesLeft t a * u a) *
      (∑ b : Fin 3, tilesRight t b * v b) = 0) : u = 0 ∨ v = 0 := by
  apply tiles_no_product u v
  rw [tilesSpace_bilinear_iff]
  intro t
  calc
    _ = (∑ a : Fin 3, tilesLeft t a * u a) *
        (∑ b : Fin 3, tilesRight t b * v b) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = 0 := h t

theorem tiles_slices_annihilate {C D : Type*}
    (X : Matrix (Fin 3 × C) (Fin 3 × D) ℂ)
    (h : ∀ c d, (fun a b => X (a,c) (b,d)) ∈ tilesSpace) :
    ∀ t c d, (∑ a : Fin 3, ∑ b : Fin 3,
      tilesLeft t a * X (a,c) (b,d) * tilesRight t b) = 0 := by
  intro t c d
  exact (tilesSpace_bilinear_iff _).mp (h c d) t

/-- A concrete nonzero rank-two coefficient matrix in the Tiles complement. -/
def tilesRankTwo : M3 := ![![1,1,-1], ![0,0,-1], ![0,0,0]]

theorem tilesRankTwo_mem : tilesRankTwo ∈ tilesSpace := by
  rw [mem_tilesSpace_iff]
  norm_num [tilesRankTwo, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem tilesRankTwo_nonzero : tilesRankTwo ≠ 0 := by
  intro h
  have he := congr_fun (congr_fun h 0) 0
  norm_num [tilesRankTwo] at he

theorem tilesRankTwo_hasSR : HasSR 2 (Function.uncurry tilesRankTwo) := by
  refine ⟨2, le_rfl, ![![1,0,0], ![0,1,0]], ![![1,1,-1], ![0,0,-1]], ?_⟩
  intro i j
  change tilesRankTwo i j = _
  fin_cases i <;> fin_cases j <;>
    norm_num [tilesRankTwo, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

end PPTCone
