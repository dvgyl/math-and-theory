import TilesBase

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace PPTCone

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The actual range of an idempotent matrix, written as a subspace of
bipartite coefficient matrices. The definition is meaningful for any matrix. -/
def projectionSpace (P : Matrix (A × B) (A × B) ℂ) :
    Submodule ℂ (Matrix A B ℂ) where
  carrier := {X | P *ᵥ Function.uncurry X = Function.uncurry X}
  zero_mem' := by
    change P *ᵥ 0 = 0
    exact Matrix.mulVec_zero P
  add_mem' := by
    intro X Y hX hY
    change P *ᵥ (Function.uncurry X + Function.uncurry Y) =
      Function.uncurry X + Function.uncurry Y
    rw [Matrix.mulVec_add, hX, hY]
  smul_mem' := by
    intro c X hX
    change P *ᵥ (c • Function.uncurry X) = c • Function.uncurry X
    rw [Matrix.mulVec_smul, hX]

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem mem_projectionSpace (P : Matrix (A × B) (A × B) ℂ)
    (X : Matrix A B ℂ) :
    X ∈ projectionSpace P ↔ P *ᵥ Function.uncurry X = Function.uncurry X := Iff.rfl

omit [DecidableEq A] [DecidableEq B] in
theorem projectionSpace_output_mem (P : Matrix (A × B) (A × B) ℂ)
    (hP : P * P = P) (x : A × B → ℂ) :
    (fun a b => (P *ᵥ x) (a,b)) ∈ projectionSpace P := by
  change P *ᵥ (P *ᵥ x) = P *ᵥ x
  rw [Matrix.mulVec_mulVec, hP]

/-- Tensor square of a bipartite operator, with the local systems regrouped. -/
def tensorSquare (P : Matrix (A × B) (A × B) ℂ) :
    Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ := fun p q =>
  P (p.1.1,p.2.1) (q.1.1,q.2.1) * P (p.1.2,p.2.2) (q.1.2,q.2.2)

theorem tensorSquare_eq_reindex (P : Matrix (A × B) (A × B) ℂ) : tensorSquare P =
    Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodProdProdComm A B A B) (P ⊗ₖ P) := rfl

theorem tensorSquare_idempotent (P : Matrix (A × B) (A × B) ℂ)
    (hP : P * P = P) : tensorSquare P * tensorSquare P = tensorSquare P := by
  rw [tensorSquare_eq_reindex, ← map_mul, ← Matrix.mul_kronecker_mul, hP]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem tensorSquare_hermitian (P : Matrix (A × B) (A × B) ℂ)
    (hP : P.IsHermitian) : (tensorSquare P).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [tensorSquare, star_mul]
  rw [hP.apply, hP.apply]
  exact mul_comm _ _

theorem tensorSquare_posSemidef (P : Matrix (A × B) (A × B) ℂ)
    (hH : P.IsHermitian) (hI : P * P = P) : (tensorSquare P).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (tensorSquare P)
  rw [(tensorSquare_hermitian P hH).eq, tensorSquare_idempotent P hI] at h
  exact h

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem tensorSquare_partialTranspose (P : Matrix (A × B) (A × B) ℂ)
    (hP : partialTranspose P = P) : partialTranspose (tensorSquare P) = tensorSquare P := by
  ext p q
  change P (p.1.1,q.2.1) (q.1.1,p.2.1) * P (p.1.2,q.2.2) (q.1.2,p.2.2) = _
  exact congrArg₂ (· * ·)
    (congr_fun (congr_fun hP (p.1.1,p.2.1)) (q.1.1,q.2.1))
    (congr_fun (congr_fun hP (p.1.2,p.2.2)) (q.1.2,q.2.2))

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem tensorSquare_nonzero (P : Matrix (A × B) (A × B) ℂ)
    (hP : P ≠ 0) : tensorSquare P ≠ 0 := by
  intro h
  apply hP
  ext ⟨a,b⟩ ⟨c,d⟩
  have he := congr_fun (congr_fun h ((a,a),(b,b))) ((c,c),(d,d))
  change P (a,b) (c,d) * P (a,b) (c,d) = 0 at he
  exact mul_self_eq_zero.mp he

omit [DecidableEq A] [DecidableEq B] in
theorem tensorSquare_output_slice_left (P : Matrix (A × B) (A × B) ℂ)
    (hP : P * P = P) (v : (A × A) × (B × B) → ℂ) (c : A) (d : B) :
    (fun a b => (tensorSquare P *ᵥ v) ((a,c),(b,d))) ∈ projectionSpace P := by
  let z : A × B → ℂ := fun q => ∑ r : A × B,
    P (c,d) r * v ((q.1,r.1),(q.2,r.2))
  have h := projectionSpace_output_mem P hP z
  convert h using 1
  ext a b
  simp only [Matrix.mulVec, dotProduct, tensorSquare, z, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro a' ha'
  exact Finset.sum_comm

omit [DecidableEq A] [DecidableEq B] in
theorem tensorSquare_output_slice_right (P : Matrix (A × B) (A × B) ℂ)
    (hP : P * P = P) (v : (A × A) × (B × B) → ℂ) (a : A) (b : B) :
    (fun c d => (tensorSquare P *ᵥ v) ((a,c),(b,d))) ∈ projectionSpace P := by
  let z : A × B → ℂ := fun r => ∑ q : A × B,
    P (a,b) q * v ((q.1,r.1),(q.2,r.2))
  have h := projectionSpace_output_mem P hP z
  convert h using 1
  ext c d
  simp only [Matrix.mulVec, dotProduct, tensorSquare, z, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c' hc'
  calc
    _ = ∑ a' : A, ∑ d' : B, ∑ b' : B,
      P (a,b) (a',b') * P (c,d) (c',d') * v ((a',c'),(b',d')) := by
      apply Finset.sum_congr rfl
      intro a' ha'
      exact Finset.sum_comm
    _ = ∑ d' : B, ∑ a' : A, ∑ b' : B,
      P (a,b) (a',b') * P (c,d) (c',d') * v ((a',c'),(b',d')) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d' hd'
      apply Finset.sum_congr rfl
      intro a' ha'
      apply Finset.sum_congr rfl
      intro b' hb'
      ring

omit [DecidableEq A] [DecidableEq B] in
theorem tensorSquare_fixed_slices (P : Matrix (A × B) (A × B) ℂ)
    (hP : P * P = P) (v : (A × A) × (B × B) → ℂ)
    (h : tensorSquare P *ᵥ v = v) :
    (∀ c d, (fun a b => v ((a,c),(b,d))) ∈ projectionSpace P) ∧
    (∀ a b, (fun c d => v ((a,c),(b,d))) ∈ projectionSpace P) := by
  constructor
  · intro c d
    rw [← h]
    exact tensorSquare_output_slice_left P hP v c d
  · intro a b
    rw [← h]
    exact tensorSquare_output_slice_right P hP v a b

theorem projectionSpace_tilesProjector : projectionSpace tilesProjector = tilesSpace := by
  apply Submodule.ext
  intro X
  constructor
  · intro h
    have hm := tilesProjector_output_mem (Function.uncurry X)
    rw [(mem_projectionSpace _ _).mp h] at hm
    exact hm
  · intro h
    exact tilesProjector_fixed X h

end
end PPTCone
