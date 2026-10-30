import UPBRank
import SchmidtUpper

open scoped Matrix BigOperators

namespace PPTCone

noncomputable section

/-- The actual regrouped coefficient matrix of a simple bipartite tensor. -/
def coefficientTensor {A B C D : Type*}
    (X : Matrix A B ℂ) (Y : Matrix C D ℂ) : Matrix (A × C) (B × D) ℂ :=
  fun i j => X i.1 j.1 * Y i.2 j.2

/-- The concrete tensor product subspace, embedded by the canonical regrouping
from (A ⊗ B) ⊗ (C ⊗ D) to (A ⊗ C) ⊗ (B ⊗ D). -/
def matrixTensorSpace {A B C D : Type*}
    (S : Submodule ℂ (Matrix A B ℂ)) (T : Submodule ℂ (Matrix C D ℂ)) :
    Submodule ℂ (Matrix (A × C) (B × D) ℂ) :=
  Submodule.span ℂ {Z | ∃ X ∈ S, ∃ Y ∈ T, Z = coefficientTensor X Y}

theorem coefficientTensor_mem {A B C D : Type*}
    (S : Submodule ℂ (Matrix A B ℂ)) (T : Submodule ℂ (Matrix C D ℂ))
    {X : Matrix A B ℂ} {Y : Matrix C D ℂ} (hX : X ∈ S) (hY : Y ∈ T) :
    coefficientTensor X Y ∈ matrixTensorSpace S T :=
  Submodule.subset_span ⟨X, hX, Y, hY, rfl⟩

theorem matrixTensorSpace_slices {A B C D : Type*}
    (S : Submodule ℂ (Matrix A B ℂ)) (T : Submodule ℂ (Matrix C D ℂ))
    {Z : Matrix (A × C) (B × D) ℂ} (hZ : Z ∈ matrixTensorSpace S T) :
    (∀ c d, (fun a b => Z (a,c) (b,d)) ∈ S) ∧
    (∀ a b, (fun c d => Z (a,c) (b,d)) ∈ T) := by
  change Z ∈ Submodule.span ℂ _ at hZ
  refine Submodule.span_induction
    (p := fun Z _ => (∀ c d, (fun a b => Z (a,c) (b,d)) ∈ S) ∧
      (∀ a b, (fun c d => Z (a,c) (b,d)) ∈ T)) ?_ ?_ ?_ ?_ hZ
  · intro Z hZ
    obtain ⟨X, hX, Y, hY, rfl⟩ := hZ
    constructor
    · intro c d
      convert S.smul_mem (Y c d) hX using 1
      ext a b
      simp [coefficientTensor, Matrix.smul_apply, mul_comm]
    · intro a b
      exact T.smul_mem (X a b) hY
  · constructor
    · intro c d
      exact S.zero_mem
    · intro a b
      exact T.zero_mem
  · intro X Y _ _ hX hY
    constructor
    · intro c d
      exact S.add_mem (hX.1 c d) (hY.1 c d)
    · intro a b
      exact T.add_mem (hX.2 a b) (hY.2 a b)
  · intro z X _ hX
    constructor
    · intro c d
      exact S.smul_mem z (hX.1 c d)
    · intro a b
      exact T.smul_mem z (hX.2 a b)

theorem coefficientTensor_nonzero {A B C D : Type*}
    {X : Matrix A B ℂ} {Y : Matrix C D ℂ} (hX : X ≠ 0) (hY : Y ≠ 0) :
    coefficientTensor X Y ≠ 0 := by
  classical
  have hx : ∃ a b, X a b ≠ 0 := by
    by_contra! hh
    apply hX
    ext a b
    exact hh a b
  have hy : ∃ c d, Y c d ≠ 0 := by
    by_contra! hh
    apply hY
    ext c d
    exact hh c d
  obtain ⟨a,b,hab⟩ := hx
  obtain ⟨c,d,hcd⟩ := hy
  intro h
  have hh := congrFun (congrFun h (a,c)) (b,d)
  exact mul_ne_zero hab hcd hh

/-- An attained minimum among ranks of all nonzero matrices in a subspace. -/
def HasMinimumRank {A B : Type*} [Fintype A] [Fintype B]
    (S : Submodule ℂ (Matrix A B ℂ)) (r : ℕ) : Prop :=
  (∀ X ∈ S, X ≠ 0 → r ≤ X.rank) ∧
  ∃ X ∈ S, X ≠ 0 ∧ X.rank = r

theorem matrix_rank_pos_of_nonzero {A B : Type*} [Fintype A] [Fintype B]
    (X : Matrix A B ℂ) (hX : X ≠ 0) : 0 < X.rank := by
  by_contra hr
  have hsr : HasSR 0 (Function.uncurry X) :=
    hasSR_of_matrix_rank_le (by omega)
  obtain ⟨r, hr, a, b, hab⟩ := hsr
  have he : r = 0 := by omega
  subst r
  apply hX
  ext i j
  simpa using hab i j

/-- A subspace cut out by an unextendible family of product functionals,
and containing a nonzero rank-at-most-two matrix, is strongly multiplicative
for minimum nonzero matrix rank against every nonzero tensor partner. -/
theorem upb_strong_minimum_rank
    {A B C D I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (α : I → A → ℂ) (β : I → B → ℂ)
    (hupb : ∀ (u : A → ℂ) (v : B → ℂ),
      (∀ t, (∑ a, α t a * u a) * (∑ b, β t b * v b) = 0) → u = 0 ∨ v = 0)
    (S : Submodule ℂ (Matrix A B ℂ))
    (hS : ∀ X ∈ S, ∀ t, ∑ a, ∑ b, α t a * X a b * β t b = 0)
    (hS2 : ∃ X ∈ S, X ≠ 0 ∧ HasSR 2 (Function.uncurry X))
    (T : Submodule ℂ (Matrix C D ℂ)) (r : ℕ) (hT : HasMinimumRank T r) :
    HasMinimumRank (matrixTensorSpace S T) (2*r) := by
  classical
  obtain ⟨Y, hY, hYne, hYr⟩ := hT.2
  have hr : 0 < r := by
    rw [← hYr]
    exact matrix_rank_pos_of_nonzero Y hYne
  have hTlow : NoSR (r-1) T := by
    intro X hX hsr
    by_contra hn
    have hmin := hT.1 X hX hn
    have hmax := hsr.matrix_rank_le
    omega
  have hlow : ∀ Z ∈ matrixTensorSpace S T, Z ≠ 0 → 2*r ≤ Z.rank := by
    intro Z hZ hn
    by_contra hh
    have hslices := matrixTensorSpace_slices S T hZ
    apply hn
    apply upb_tensor_no_sr α β hupb (r-1) T hTlow Z hslices.2
    · intro t c d
      exact hS _ (hslices.1 c d) t
    · apply hasSR_of_matrix_rank_le
      omega
  refine ⟨hlow, ?_⟩
  obtain ⟨X, hX, hXne, hXsr⟩ := hS2
  have hm := coefficientTensor_mem S T hX hY
  have hn := coefficientTensor_nonzero hXne hYne
  refine ⟨coefficientTensor X Y, hm, hn, le_antisymm ?_ (hlow _ hm hn)⟩
  have hYsr : HasSR r (Function.uncurry Y) := hasSR_of_matrix_rank_le hYr.le
  exact (hXsr.tensor hYsr).matrix_rank_le

/-- The Tiles complement has exact minimum rank twice that of every nonzero
matrix subspace, under the actual tensor-product regrouping. -/
theorem tiles_strong_minimum_rank
    {C D : Type*} [Fintype C] [Fintype D]
    (T : Submodule ℂ (Matrix C D ℂ)) (r : ℕ) (hT : HasMinimumRank T r) :
    HasMinimumRank (matrixTensorSpace tilesSpace T) (2*r) := by
  apply upb_strong_minimum_rank tilesLeft tilesRight tiles_unextendible tilesSpace
  · intro X hX t
    exact (tilesSpace_bilinear_iff X).mp hX t
  · exact ⟨tilesRankTwo, tilesRankTwo_mem, tilesRankTwo_nonzero, tilesRankTwo_hasSR⟩
  · exact hT

#print axioms upb_strong_minimum_rank
#print axioms tiles_strong_minimum_rank

end
end PPTCone
