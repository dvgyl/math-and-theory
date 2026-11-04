module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.Block
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace MatCKronecker

open Matrix

variable {m n κ : Type*}

/-- Literal entrywise nonnegativity; this is not the Loewner order. -/
def EntryNonneg (A : Matrix m n ℝ) : Prop := ∀ i j, 0 ≤ A i j

/-- An actual entrywise nonnegative real factorization with exactly `k` inner
coordinates. Zero columns/rows are permitted, so the width may be padded. -/
def HasNMF (A : Matrix m n ℝ) (k : ℕ) : Prop :=
  ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix (Fin k) n ℝ,
    EntryNonneg U ∧ EntryNonneg V ∧ U * V = A

/-- The minimum nonnegative factorization width. On a matrix with a negative
entry the defining set is empty, and this total definition returns zero.
Every theorem identifying this with nonnegative rank assumes entrywise
nonnegativity or supplies an actual nonnegative factorization. -/
noncomputable def nnrank (A : Matrix m n ℝ) : ℕ := by
  classical
  exact if h : ∃ k, HasNMF A k then Nat.find h else 0

theorem hasNMF_of_factorization [Fintype κ]
    {A : Matrix m n ℝ} (U : Matrix m κ ℝ) (V : Matrix κ n ℝ)
    (hU : EntryNonneg U) (hV : EntryNonneg V) (hUV : U * V = A) :
    HasNMF A (Fintype.card κ) := by
  classical
  let e := (Fintype.equivFin κ).symm
  refine ⟨U.submatrix id e, V.submatrix e id, ?_, ?_, ?_⟩
  · intro i j
    exact hU i (e j)
  · intro i j
    exact hV (e i) j
  · rw [Matrix.submatrix_mul_equiv]
    simpa using congrArg (fun M : Matrix m n ℝ => M.submatrix id id) hUV

theorem HasNMF.nonneg {A : Matrix m n ℝ} {k : ℕ} (h : HasNMF A k) : EntryNonneg A := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (hU i t) (hV t j)

theorem exists_hasNMF [Fintype n] {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    ∃ k, HasNMF A k := by
  classical
  refine ⟨Fintype.card n, hasNMF_of_factorization A (1 : Matrix n n ℝ) hA ?_ ?_⟩
  · intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · simp

theorem nnrank_le_of_hasNMF {A : Matrix m n ℝ} {k : ℕ} (h : HasNMF A k) :
    nnrank A ≤ k := by
  classical
  rw [nnrank, dite_eq_left ⟨k, h⟩]
  exact Nat.find_min' ⟨k, h⟩ h

theorem hasNMF_nnrank [Fintype n] {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    HasNMF A (nnrank A) := by
  classical
  rw [nnrank, dite_eq_left (exists_hasNMF hA)]
  exact Nat.find_spec (exists_hasNMF hA)

theorem HasNMF.rank_le [Fintype n] {A : Matrix m n ℝ} {k : ℕ} (h : HasNMF A k) :
    A.rank ≤ k := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h
  exact (Matrix.rank_mul_le_left U V).trans (by simpa using U.rank_le_card_width)

theorem rank_le_nnrank [Fintype n] {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    A.rank ≤ nnrank A :=
  (hasNMF_nnrank hA).rank_le

theorem nnrank_le_card_width [Fintype n] {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    nnrank A ≤ Fintype.card n := by
  classical
  apply nnrank_le_of_hasNMF
  exact hasNMF_of_factorization A 1 hA
    (by intro i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]) (by simp)

theorem HasNMF.mono {A : Matrix m n ℝ} {k l : ℕ}
    (h : HasNMF A k) (hkl : k ≤ l) : HasNMF A l := by
  classical
  obtain ⟨U, V, hU, hV, hUV⟩ := h
  let U' : Matrix m (Fin k ⊕ Fin (l - k)) ℝ := fun i j =>
    Sum.elim (U i) (fun _ => 0) j
  let V' : Matrix (Fin k ⊕ Fin (l - k)) n ℝ := fun i j =>
    Sum.elim (fun t => V t j) (fun _ => 0) i
  have hU' : EntryNonneg U' := by
    intro i j
    cases j with
    | inl t => exact hU i t
    | inr t => exact le_rfl
  have hV' : EntryNonneg V' := by
    intro i j
    cases i with
    | inl t => exact hV t j
    | inr t => exact le_rfl
  have hUV' : U' * V' = A := by
    ext i j
    rw [Matrix.mul_apply]
    simpa [Matrix.mul_apply, U', V', Fintype.sum_sum_type] using congrArg (fun M => M i j) hUV
  have hc : Fintype.card (Fin k ⊕ Fin (l - k)) = l := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  simpa only [hc] using hasNMF_of_factorization U' V' hU' hV' hUV'

theorem nnrank_le_iff [Fintype n] {A : Matrix m n ℝ} (hA : EntryNonneg A) (k : ℕ) :
    nnrank A ≤ k ↔ HasNMF A k :=
  ⟨fun h => (hasNMF_nnrank hA).mono h, nnrank_le_of_hasNMF⟩

theorem hasNMF_zero : HasNMF (0 : Matrix m n ℝ) 0 := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · exact fun _ _ => le_rfl
  · exact fun _ _ => le_rfl
  · simp

@[simp] theorem nnrank_zero : nnrank (0 : Matrix m n ℝ) = 0 :=
  Nat.eq_zero_of_le_zero (nnrank_le_of_hasNMF hasNMF_zero)

theorem HasNMF.submatrix {m' n' : Type*} {A : Matrix m n ℝ} {k : ℕ}
    (h : HasNMF A k) (f : m' → m) (g : n' → n) : HasNMF (A.submatrix f g) k := by
  obtain ⟨U, V, hU, hV, hUV⟩ := h
  refine ⟨U.submatrix f id, V.submatrix id g, ?_, ?_, ?_⟩
  · exact fun i j => hU (f i) j
  · exact fun i j => hV i (g j)
  · simpa only [← Matrix.submatrix_mul U V f id g Function.bijective_id] using
      congrArg (fun M : Matrix m n ℝ => M.submatrix f g) hUV

theorem hasNMF_submatrix_equiv_iff {m' n' : Type*} {A : Matrix m n ℝ} {k : ℕ}
    (f : m' ≃ m) (g : n' ≃ n) : HasNMF (A.submatrix f g) k ↔ HasNMF A k := by
  constructor
  · intro h
    simpa using h.submatrix f.symm g.symm
  · exact fun h => h.submatrix f g

theorem nnrank_submatrix_equiv [Fintype n] {m' n' : Type*} [Fintype n']
    {A : Matrix m n ℝ} (hA : EntryNonneg A) (f : m' ≃ m) (g : n' ≃ n) :
    nnrank (A.submatrix f g) = nnrank A := by
  apply le_antisymm
  · exact nnrank_le_of_hasNMF ((hasNMF_nnrank hA).submatrix f g)
  · have hsub : EntryNonneg (A.submatrix f g) := fun i j => hA (f i) (g j)
    exact nnrank_le_of_hasNMF ((hasNMF_submatrix_equiv_iff f g).mp (hasNMF_nnrank hsub))

end MatCKronecker
