import BlockRank
import RankBridge

set_option maxHeartbeats 400000

open scoped Matrix BigOperators

namespace PPTCone

noncomputable section

def leftLocalContraction {A C : Type*} [DecidableEq C]
    (a : A → ℂ) : Matrix C (A × C) ℂ :=
  fun c p => if c = p.2 then a p.1 else 0

def rightLocalContraction {B D : Type*} [DecidableEq D]
    (b : B → ℂ) : Matrix (B × D) D ℂ :=
  fun p d => if p.2 = d then b p.1 else 0

theorem leftLocalContraction_mul
    {A B C D : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (a : A → ℂ) (X : Matrix (A × C) (B × D) ℂ) (c : C) (b : B) (d : D) :
    (leftLocalContraction (C := C) a * X) c (b,d) = ∑ i, a i * X (i,c) (b,d) := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_prod_type, leftLocalContraction]

theorem mul_rightLocalContraction
    {A B C D : Type*} [Fintype B] [Fintype D] [DecidableEq D]
    (b : B → ℂ) (X : Matrix (A × C) (B × D) ℂ) (a : A) (c : C) (d : D) :
    (X * rightLocalContraction (D := D) b) (a,c) d = ∑ j, X (a,c) (j,d) * b j := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_prod_type, rightLocalContraction]

theorem localContraction_mul_both
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D]
    (a : A → ℂ) (b : B → ℂ) (X : Matrix (A × C) (B × D) ℂ)
    (c : C) (d : D) :
    (leftLocalContraction (C := C) a * X * rightLocalContraction (D := D) b) c d =
      ∑ i, ∑ j, a i * X (i,c) (j,d) * b j := by
  classical
  change (∑ p : B × D, (leftLocalContraction (C := C) a * X) c p *
    rightLocalContraction (D := D) b p d) = _
  simp only [Fintype.sum_prod_type, rightLocalContraction, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [leftLocalContraction_mul, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem noSR_rank_gt_of_ne_zero
    {C D : Type*} [Fintype C] [Fintype D] {k : ℕ}
    (T : Submodule ℂ (Matrix C D ℂ)) (hT : NoSR k T)
    (R : Matrix C D ℂ) (hR : R ∈ T) (hn : R ≠ 0) : k < R.rank := by
  by_contra h
  exact hn (hT R hR (hasSR_of_matrix_rank_le (Nat.le_of_not_gt h)))

/-- For a matrix with blocks in a subspace of minimum nonzero rank k+1,
a zero local corner forces an entire local row or column to vanish whenever
the matrix has rank at most 2k+1. -/
theorem local_annihilation_dichotomy
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D]
    (k : ℕ) (T : Submodule ℂ (Matrix C D ℂ)) (hT : NoSR k T)
    (X : Matrix (A × C) (B × D) ℂ)
    (hmem : ∀ a b, (fun c d => X (a,c) (b,d)) ∈ T)
    (a : A → ℂ) (b : B → ℂ)
    (hz : leftLocalContraction (C := C) a * X * rightLocalContraction (D := D) b = 0)
    (hrank : X.rank ≤ 2*k+1) :
    leftLocalContraction (C := C) a * X = 0 ∨ X * rightLocalContraction (D := D) b = 0 := by
  classical
  by_cases hl : leftLocalContraction (C := C) a * X = 0
  · exact Or.inl hl
  right
  by_contra hr
  have hexl : ∃ c j d, (leftLocalContraction (C := C) a * X) c (j,d) ≠ 0 := by
    by_contra! hh
    apply hl
    ext c ⟨j,d⟩
    exact hh c j d
  have hexr : ∃ i c d, (X * rightLocalContraction (D := D) b) (i,c) d ≠ 0 := by
    by_contra! hh
    apply hr
    ext ⟨i,c⟩ d
    exact hh i c d
  obtain ⟨c₀,j₀,d₀,hlne⟩ := hexl
  obtain ⟨i₁,c₁,d₁,hrne⟩ := hexr
  let L : Matrix C D ℂ := fun c d => (leftLocalContraction (C := C) a * X) c (j₀,d)
  let R : Matrix C D ℂ := fun c d => (X * rightLocalContraction (D := D) b) (i₁,c) d
  have hL : L ∈ T := by
    have hh := T.sum_mem (fun i (_ : i ∈ Finset.univ) => T.smul_mem (a i) (hmem i j₀))
    convert hh using 1
    ext c d
    simp [L, leftLocalContraction_mul, Matrix.sum_apply, Matrix.smul_apply]
  have hR : R ∈ T := by
    have hh := T.sum_mem (fun j (_ : j ∈ Finset.univ) => T.smul_mem (b j) (hmem i₁ j))
    convert hh using 1
    ext c d
    simp [R, mul_rightLocalContraction, Matrix.sum_apply, Matrix.smul_apply, mul_comm]
  have hLne : L ≠ 0 := by
    intro hh
    exact hlne (congrFun (congrFun hh c₀) d₀)
  have hRne : R ≠ 0 := by
    intro hh
    exact hrne (congrFun (congrFun hh c₁) d₁)
  have hLrank := noSR_rank_gt_of_ne_zero T hT L hL hLne
  have hRrank := noSR_rank_gt_of_ne_zero T hT R hR hRne
  have hLle : L.rank ≤ (leftLocalContraction (C := C) a * X).rank :=
    rank_select_columns_le (leftLocalContraction (C := C) a * X) (fun d => (j₀,d))
  have hRle : R.rank ≤ (X * rightLocalContraction (D := D) b).rank :=
    rank_select_rows_le (X * rightLocalContraction (D := D) b) (fun c => (i₁,c))
  have hsum := rank_compressions_add_le X (leftLocalContraction (C := C) a)
    (rightLocalContraction (D := D) b) hz
  omega

/-- An unextendible family of product annihilators doubles the minimum
nonzero rank of every tensor factor. The assumptions apply to the actual
regrouped matrix, via its local slices and all bilinear annihilation constraints. -/
theorem upb_tensor_no_sr
    {A B C D I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (α : I → A → ℂ) (β : I → B → ℂ)
    (hupb : ∀ (u : A → ℂ) (v : B → ℂ), (∀ t, (∑ a, α t a * u a) * (∑ b, β t b * v b) = 0) →
      u = 0 ∨ v = 0)
    (k : ℕ) (T : Submodule ℂ (Matrix C D ℂ)) (hT : NoSR k T)
    (X : Matrix (A × C) (B × D) ℂ)
    (hmem : ∀ a b, (fun c d => X (a,c) (b,d)) ∈ T)
    (hzero : ∀ t c d, ∑ a, ∑ b, α t a * X (a,c) (b,d) * β t b = 0)
    (hrank : HasSR (2*k+1) (Function.uncurry X)) : X = 0 := by
  classical
  by_contra hX
  have hex : ∃ a c b d, X (a,c) (b,d) ≠ 0 := by
    by_contra! hh
    apply hX
    ext ⟨a,c⟩ ⟨b,d⟩
    exact hh a c b d
  obtain ⟨a₀,c₀,b₀,d₀,hentry⟩ := hex
  let u : A → ℂ := fun a => X (a,c₀) (b₀,d₀)
  let v : B → ℂ := fun b => X (a₀,c₀) (b,d₀)
  have hu : u ≠ 0 := by
    intro hh
    exact hentry (congrFun hh a₀)
  have hv : v ≠ 0 := by
    intro hh
    exact hentry (congrFun hh b₀)
  have he := hupb u v (by
    intro t
    have hz : leftLocalContraction (C := C) (α t) * X * rightLocalContraction (D := D) (β t) = 0 := by
      ext c d
      simpa only [localContraction_mul_both, Matrix.zero_apply] using hzero t c d
    rcases local_annihilation_dichotomy k T hT X hmem (α t) (β t) hz
      hrank.matrix_rank_le with hl | hr
    · have hh := congrFun (congrFun hl c₀) (b₀,d₀)
      have hz' : ∑ a, α t a * u a = 0 := by
        simpa only [leftLocalContraction_mul, Matrix.zero_apply, u] using hh
      rw [hz', zero_mul]
    · have hh := congrFun (congrFun hr (a₀,c₀)) d₀
      have hz' : ∑ b, β t b * v b = 0 := by
        simpa only [mul_rightLocalContraction, Matrix.zero_apply, v, mul_comm] using hh
      rw [hz', mul_zero])
  exact he.elim hu hv

end
end PPTCone
