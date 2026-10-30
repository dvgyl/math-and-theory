import TensorProjection

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace PPTCone

noncomputable section

variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Tensor product of two bipartite operators, with their local systems regrouped. -/
def tensorProduct (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ) :
    Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ := fun p q =>
  P (p.1.1,p.2.1) (q.1.1,q.2.1) * Q (p.1.2,p.2.2) (q.1.2,q.2.2)

theorem tensorProduct_eq_reindex (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ) : tensorProduct P Q =
    Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodProdProdComm A B C D) (P ⊗ₖ Q) := rfl

theorem tensorProduct_idempotent (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ) (hP : P * P = P) (hQ : Q * Q = Q) :
    tensorProduct P Q * tensorProduct P Q = tensorProduct P Q := by
  rw [tensorProduct_eq_reindex, ← map_mul, ← Matrix.mul_kronecker_mul, hP, hQ]

omit [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem tensorProduct_hermitian (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    (tensorProduct P Q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [tensorProduct, star_mul]
  rw [hP.apply, hQ.apply]
  exact mul_comm _ _

theorem tensorProduct_posSemidef (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ)
    (hHP : P.IsHermitian) (hHQ : Q.IsHermitian) (hIP : P * P = P) (hIQ : Q * Q = Q) :
    (tensorProduct P Q).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (tensorProduct P Q)
  rw [(tensorProduct_hermitian P Q hHP hHQ).eq,
    tensorProduct_idempotent P Q hIP hIQ] at h
  exact h

omit [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem tensorProduct_partialTranspose (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ)
    (hP : partialTranspose P = P) (hQ : partialTranspose Q = Q) :
    partialTranspose (tensorProduct P Q) = tensorProduct P Q := by
  ext p q
  change P (p.1.1,q.2.1) (q.1.1,p.2.1) * Q (p.1.2,q.2.2) (q.1.2,p.2.2) = _
  exact congrArg₂ (· * ·)
    (congr_fun (congr_fun hP (p.1.1,p.2.1)) (q.1.1,q.2.1))
    (congr_fun (congr_fun hQ (p.1.2,p.2.2)) (q.1.2,q.2.2))

omit [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem tensorProduct_nonzero (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    tensorProduct P Q ≠ 0 := by
  intro h
  apply hP
  ext ⟨a,b⟩ ⟨a',b'⟩
  by_contra hp
  apply hQ
  ext ⟨c,d⟩ ⟨c',d'⟩
  have he := congr_fun (congr_fun h ((a,c),(b,d))) ((a',c'),(b',d'))
  change P (a,b) (a',b') * Q (c,d) (c',d') = 0 at he
  exact (mul_eq_zero.mp he).resolve_left hp

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem tensorProduct_output_slice_left (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ)
    (hP : P * P = P) (v : (A × C) × (B × D) → ℂ) (c : C) (d : D) :
    (fun a b => (tensorProduct P Q *ᵥ v) ((a,c),(b,d))) ∈ projectionSpace P := by
  let z : A × B → ℂ := fun q => ∑ r : C × D,
    Q (c,d) r * v ((q.1,r.1),(q.2,r.2))
  have h := projectionSpace_output_mem P hP z
  convert h using 1
  ext a b
  simp only [Matrix.mulVec, dotProduct, tensorProduct, z, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro a' _
  exact Finset.sum_comm

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem tensorProduct_output_slice_right (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ)
    (hQ : Q * Q = Q) (v : (A × C) × (B × D) → ℂ) (a : A) (b : B) :
    (fun c d => (tensorProduct P Q *ᵥ v) ((a,c),(b,d))) ∈ projectionSpace Q := by
  let z : C × D → ℂ := fun r => ∑ q : A × B,
    P (a,b) q * v ((q.1,r.1),(q.2,r.2))
  have h := projectionSpace_output_mem Q hQ z
  convert h using 1
  ext c d
  simp only [Matrix.mulVec, dotProduct, tensorProduct, z, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c' _
  calc
    _ = ∑ a' : A, ∑ d' : D, ∑ b' : B,
      P (a,b) (a',b') * Q (c,d) (c',d') * v ((a',c'),(b',d')) := by
      apply Finset.sum_congr rfl
      intro a' _
      exact Finset.sum_comm
    _ = ∑ d' : D, ∑ a' : A, ∑ b' : B,
      P (a,b) (a',b') * Q (c,d) (c',d') * v ((a',c'),(b',d')) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d' _
      apply Finset.sum_congr rfl
      intro a' _
      apply Finset.sum_congr rfl
      intro b' _
      ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem tensorProduct_fixed_slices (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ) (hP : P * P = P) (hQ : Q * Q = Q)
    (v : (A × C) × (B × D) → ℂ) (h : tensorProduct P Q *ᵥ v = v) :
    (∀ c d, (fun a b => v ((a,c),(b,d))) ∈ projectionSpace P) ∧
    (∀ a b, (fun c d => v ((a,c),(b,d))) ∈ projectionSpace Q) := by
  constructor
  · intro c d
    rw [← h]
    exact tensorProduct_output_slice_left P Q hP v c d
  · intro a b
    rw [← h]
    exact tensorProduct_output_slice_right P Q hQ v a b

end
end PPTCone
