import TilesBase

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace PPTCone

noncomputable section

/-- Two Tiles-complement projections, regrouped across A₁A₂ : B₁B₂. -/
def tilesTensor : Matrix (I9 × I9) (I9 × I9) ℂ := fun p q =>
  tilesProjector (p.1.1,p.2.1) (q.1.1,q.2.1) *
  tilesProjector (p.1.2,p.2.2) (q.1.2,q.2.2)

def tilesRegroup : I9 × I9 ≃ I9 × I9 :=
  Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin 3) (Fin 3)

theorem tilesTensor_eq_reindex : tilesTensor =
    Matrix.reindexAlgEquiv ℂ ℂ tilesRegroup (tilesProjector ⊗ₖ tilesProjector) := rfl

theorem tilesTensor_idempotent : tilesTensor * tilesTensor = tilesTensor := by
  rw [tilesTensor_eq_reindex, ← map_mul, ← Matrix.mul_kronecker_mul,
    tilesProjector_idempotent]

theorem tilesTensor_hermitian : tilesTensor.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [tilesTensor, star_mul]
  rw [tilesProjector_hermitian.apply, tilesProjector_hermitian.apply]
  exact mul_comm _ _

theorem tilesTensor_posSemidef : tilesTensor.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self tilesTensor
  rw [tilesTensor_hermitian.eq, tilesTensor_idempotent] at h
  exact h

theorem tilesTensor_partialTranspose : partialTranspose tilesTensor = tilesTensor := by
  ext p q
  change
    tilesProjector (p.1.1,q.2.1) (q.1.1,p.2.1) *
      tilesProjector (p.1.2,q.2.2) (q.1.2,p.2.2) = _
  exact congrArg₂ (· * ·)
    (congr_fun (congr_fun tilesProjector_partialTranspose (p.1.1,p.2.1))
      (q.1.1,q.2.1))
    (congr_fun (congr_fun tilesProjector_partialTranspose (p.1.2,p.2.2))
      (q.1.2,q.2.2))

theorem tilesTensor_nonzero : tilesTensor ≠ 0 := by
  intro h
  have he := congr_fun (congr_fun h ((1,1),(1,1))) ((1,1),(1,1))
  norm_num [tilesTensor, tilesProjector, tilesVector, tilesLeft, tilesRight, tilesWeight,
    Matrix.one_apply, Matrix.vecMulVec, Fin.sum_univ_succ, Prod.ext_iff, Fin.ext_iff, Fin.ofNat'] at he

theorem tilesTensor_output_slice_left (v : I9 × I9 → ℂ) (c d : Fin 3) :
    (fun a b => (tilesTensor *ᵥ v) ((a,c),(b,d))) ∈ tilesSpace := by
  let z : I9 → ℂ := fun q => ∑ r : I9,
    tilesProjector (c,d) r * v ((q.1,r.1),(q.2,r.2))
  have h := tilesProjector_output_mem z
  convert h using 1
  ext a b
  simp only [Matrix.mulVec, dotProduct, tilesTensor, z, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro a' ha'
  exact Finset.sum_comm

theorem tilesTensor_output_slice_right (v : I9 × I9 → ℂ) (a b : Fin 3) :
    (fun c d => (tilesTensor *ᵥ v) ((a,c),(b,d))) ∈ tilesSpace := by
  let z : I9 → ℂ := fun r => ∑ q : I9,
    tilesProjector (a,b) q * v ((q.1,r.1),(q.2,r.2))
  have h := tilesProjector_output_mem z
  convert h using 1
  ext c d
  simp only [Matrix.mulVec, dotProduct, tilesTensor, z, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c' hc'
  calc
    _ = ∑ a' : Fin 3, ∑ d' : Fin 3, ∑ b' : Fin 3,
      tilesProjector (a,b) (a',b') * tilesProjector (c,d) (c',d') *
        v ((a',c'),(b',d')) := by
      apply Finset.sum_congr rfl
      intro a' ha'
      exact Finset.sum_comm
    _ = ∑ d' : Fin 3, ∑ a' : Fin 3, ∑ b' : Fin 3,
      tilesProjector (a,b) (a',b') * tilesProjector (c,d) (c',d') *
        v ((a',c'),(b',d')) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d' hd'
      apply Finset.sum_congr rfl
      intro a' ha'
      apply Finset.sum_congr rfl
      intro b' hb'
      ring

theorem tilesTensor_fixed_slices (v : I9 × I9 → ℂ)
    (h : tilesTensor *ᵥ v = v) :
    (∀ c d, (fun a b => v ((a,c),(b,d))) ∈ tilesSpace) ∧
    (∀ a b, (fun c d => v ((a,c),(b,d))) ∈ tilesSpace) := by
  constructor
  · intro c d
    rw [← h]
    exact tilesTensor_output_slice_left v c d
  · intro a b
    rw [← h]
    exact tilesTensor_output_slice_right v a b

end
end PPTCone
