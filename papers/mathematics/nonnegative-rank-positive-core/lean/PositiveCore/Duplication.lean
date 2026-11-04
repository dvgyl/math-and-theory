module

public import MatCKronecker.BasicFactorizations

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped BigOperators

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]

/-- Retain every old latent coordinate and append `k` copies of the selected
coordinate. -/
def duplicateD (h0 : p) (k : ℕ) : Matrix p (p ⊕ Fin k) ℝ :=
  fun i j => match j with
    | .inl j => if i = j then 1 else 0
    | .inr _ => if i = h0 then 1 else 0

/-- Split the selected right-factor row equally between its old copy and the
`k` new copies.  All other right-factor rows are retained. -/
noncomputable def duplicateE (h0 : p) (k : ℕ) : Matrix (p ⊕ Fin k) p ℝ :=
  fun i j => match i with
    | .inl i => if i = j then (if i = h0 then ((k : ℝ) + 1)⁻¹ else 1) else 0
    | .inr _ => if h0 = j then ((k : ℝ) + 1)⁻¹ else 0

theorem duplicateD_mul_duplicateE (h0 : p) (k : ℕ) :
    duplicateD h0 k * duplicateE h0 k = 1 := by
  classical
  ext i j
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  by_cases hi : i = h0
  · subst i
    by_cases hj : h0 = j
    · subst j
      simp [Matrix.mul_apply, duplicateD, duplicateE, Fintype.sum_sum_type,
        mul_ite, ite_mul]
      field_simp
      ring
    · simp [Matrix.mul_apply, duplicateD, duplicateE, Fintype.sum_sum_type,
        mul_ite, ite_mul, hj]
  · by_cases hij : i = j
    · subst j
      simp [Matrix.mul_apply, duplicateD, duplicateE, Fintype.sum_sum_type,
        mul_ite, ite_mul, hi, Ne.symm hi]
    · simp [Matrix.mul_apply, duplicateD, duplicateE, Fintype.sum_sum_type,
        mul_ite, ite_mul, hi, hij]

/-- The duplicated left factor. -/
def duplicateLeft (U : Matrix m p ℝ) (h0 : p) (k : ℕ) : Matrix m (p ⊕ Fin k) ℝ :=
  U * duplicateD h0 k

/-- The duplicated right factor. -/
noncomputable def duplicateRight (V : Matrix p n ℝ) (h0 : p) (k : ℕ) : Matrix (p ⊕ Fin k) n ℝ :=
  duplicateE h0 k * V

@[simp] theorem duplicateLeft_inl (U : Matrix m p ℝ) (h0 : p) (k : ℕ)
    (i : m) (j : p) : duplicateLeft U h0 k i (.inl j) = U i j := by
  classical
  simp [duplicateLeft, duplicateD, Matrix.mul_apply, mul_ite]

@[simp] theorem duplicateLeft_inr (U : Matrix m p ℝ) (h0 : p) (k : ℕ)
    (i : m) (j : Fin k) : duplicateLeft U h0 k i (.inr j) = U i h0 := by
  classical
  simp [duplicateLeft, duplicateD, Matrix.mul_apply, mul_ite]

@[simp] theorem duplicateRight_inl (V : Matrix p n ℝ) (h0 : p) (k : ℕ)
    (i : p) (j : n) :
    duplicateRight V h0 k (.inl i) j =
      (if i = h0 then ((k : ℝ) + 1)⁻¹ else 1) * V i j := by
  classical
  simp [duplicateRight, duplicateE, Matrix.mul_apply, ite_mul]

@[simp] theorem duplicateRight_inr (V : Matrix p n ℝ) (h0 : p) (k : ℕ)
    (i : Fin k) (j : n) :
    duplicateRight V h0 k (.inr i) j = ((k : ℝ) + 1)⁻¹ * V h0 j := by
  classical
  simp [duplicateRight, duplicateE, Matrix.mul_apply, ite_mul]

theorem duplicateLeft_pos (U : Matrix m p ℝ) (h0 : p) (k : ℕ)
    (hU : ∀ i j, 0 < U i j) : ∀ i j, 0 < duplicateLeft U h0 k i j := by
  intro i j
  cases j with
  | inl j => simpa using hU i j
  | inr j => simpa using hU i h0

theorem duplicateRight_pos (V : Matrix p n ℝ) (h0 : p) (k : ℕ)
    (hV : ∀ i j, 0 < V i j) : ∀ i j, 0 < duplicateRight V h0 k i j := by
  intro i j
  have hk : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
  cases i with
  | inl i =>
    rw [duplicateRight_inl]
    split_ifs
    · exact mul_pos hk (hV i j)
    · simpa using hV i j
  | inr i =>
    rw [duplicateRight_inr]
    exact mul_pos hk (hV h0 j)

/-- Duplication changes the number of terms but not the represented matrix. -/
theorem duplicate_product (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (h0 : p) (k : ℕ) :
    duplicateLeft U h0 k * duplicateRight V h0 k = U * V := by
  unfold duplicateLeft duplicateRight
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (duplicateD h0 k),
    duplicateD_mul_duplicateE, Matrix.one_mul]

/-- Duplicating a column preserves the ordinary rank of the left factor. -/
theorem duplicateLeft_rank (U : Matrix m p ℝ) (h0 : p) (k : ℕ) :
    (duplicateLeft U h0 k).rank = U.rank := by
  classical
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  have hrecover : duplicateLeft U h0 k * duplicateE h0 k = U := by
    unfold duplicateLeft
    rw [Matrix.mul_assoc, duplicateD_mul_duplicateE, Matrix.mul_one]
  calc
    U.rank = (duplicateLeft U h0 k * duplicateE h0 k).rank :=
      congrArg Matrix.rank hrecover.symm
    _ ≤ (duplicateLeft U h0 k).rank := Matrix.rank_mul_le_left _ _

/-- Splitting and copying a row preserves the ordinary rank of the right
factor.  The recovery matrix is the same `D` used for the left factor. -/
theorem duplicateRight_rank (V : Matrix p n ℝ) (h0 : p) (k : ℕ) :
    (duplicateRight V h0 k).rank = V.rank := by
  classical
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  have hrecover : duplicateD h0 k * duplicateRight V h0 k = V := by
    unfold duplicateRight
    rw [← Matrix.mul_assoc, duplicateD_mul_duplicateE, Matrix.one_mul]
  calc
    V.rank = (duplicateD h0 k * duplicateRight V h0 k).rank :=
      congrArg Matrix.rank hrecover.symm
    _ ≤ (duplicateRight V h0 k).rank := Matrix.rank_mul_le_right _ _

/-- Any chosen positive summand can be duplicated arbitrarily often while
preserving strict positivity, the product, and both factor ranks. -/
theorem exists_positive_duplication (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (hU : ∀ i j, 0 < U i j) (hV : ∀ i j, 0 < V i j)
    (h0 : p) (k : ℕ) :
    ∃ U' : Matrix m (p ⊕ Fin k) ℝ, ∃ V' : Matrix (p ⊕ Fin k) n ℝ,
      (∀ i j, 0 < U' i j) ∧ (∀ i j, 0 < V' i j) ∧
      U' * V' = U * V ∧ U'.rank = U.rank ∧ V'.rank = V.rank := by
  exact ⟨duplicateLeft U h0 k, duplicateRight V h0 k,
    duplicateLeft_pos U h0 k hU, duplicateRight_pos V h0 k hV,
    duplicate_product U V h0 k, duplicateLeft_rank U h0 k,
    duplicateRight_rank V h0 k⟩

end PositiveCore
