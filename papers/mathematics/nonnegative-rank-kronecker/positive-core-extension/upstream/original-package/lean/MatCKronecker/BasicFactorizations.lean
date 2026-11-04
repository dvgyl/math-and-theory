module

public import MatCKronecker.NonnegativeRank
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

namespace MatCKronecker

open Matrix
open scoped Kronecker

variable {m n p q κ : Type*}

theorem factor_term_le [Fintype κ]
    (U : Matrix m κ ℝ) (V : Matrix κ n ℝ)
    (hU : EntryNonneg U) (hV : EntryNonneg V) (i : m) (j : n) (t : κ) :
    U i t * V t j ≤ (U * V) i j := by
  rw [Matrix.mul_apply]
  exact Finset.single_le_sum (fun s _ => mul_nonneg (hU i s) (hV s j)) (Finset.mem_univ t)

theorem EntryNonneg.transpose {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    EntryNonneg A.transpose :=
  fun i j => hA j i

theorem HasNMF.transpose {A : Matrix m n ℝ} {k : ℕ} (h : HasNMF A k) :
    HasNMF A.transpose k := by
  obtain ⟨U, V, hU, hV, hUV⟩ := h
  refine ⟨V.transpose, U.transpose, hV.transpose, hU.transpose, ?_⟩
  rw [← Matrix.transpose_mul, hUV]

theorem nnrank_transpose [Fintype m] [Fintype n]
    {A : Matrix m n ℝ} (hA : EntryNonneg A) : nnrank A.transpose = nnrank A := by
  apply le_antisymm
  · exact nnrank_le_of_hasNMF ((hasNMF_nnrank hA).transpose)
  · simpa using nnrank_le_of_hasNMF ((hasNMF_nnrank hA.transpose).transpose)

theorem EntryNonneg.kronecker {A : Matrix m n ℝ} {B : Matrix p q ℝ}
    (hA : EntryNonneg A) (hB : EntryNonneg B) : EntryNonneg (A ⊗ₖ B) :=
  fun i j => mul_nonneg (hA i.1 j.1) (hB i.2 j.2)

theorem HasNMF.kronecker {A : Matrix m n ℝ} {B : Matrix p q ℝ} {a b : ℕ}
    (hA : HasNMF A a) (hB : HasNMF B b) : HasNMF (A ⊗ₖ B) (a * b) := by
  obtain ⟨UA, VA, hUA, hVA, hA⟩ := hA
  obtain ⟨UB, VB, hUB, hVB, hB⟩ := hB
  have h := hasNMF_of_factorization (A := A ⊗ₖ B)
    (UA ⊗ₖ UB) (VA ⊗ₖ VB) (hUA.kronecker hUB) (hVA.kronecker hVB) (by
      rw [← Matrix.mul_kronecker_mul, hA, hB])
  simpa only [Fintype.card_prod, Fintype.card_fin] using h

theorem nnrank_kronecker_le [Fintype n] [Fintype q]
    {A : Matrix m n ℝ} {B : Matrix p q ℝ}
    (hA : EntryNonneg A) (hB : EntryNonneg B) :
    nnrank (A ⊗ₖ B) ≤ nnrank A * nnrank B :=
  nnrank_le_of_hasNMF ((hasNMF_nnrank hA).kronecker (hasNMF_nnrank hB))

theorem HasNMF.add {A B : Matrix m n ℝ} {a b : ℕ}
    (hA : HasNMF A a) (hB : HasNMF B b) : HasNMF (A + B) (a + b) := by
  obtain ⟨UA, VA, hUA, hVA, hA⟩ := hA
  obtain ⟨UB, VB, hUB, hVB, hB⟩ := hB
  have hU : EntryNonneg (Matrix.fromCols UA UB) := by
    intro i j
    cases j with
    | inl j => exact hUA i j
    | inr j => exact hUB i j
  have hV : EntryNonneg (Matrix.fromRows VA VB) := by
    intro i j
    cases i with
    | inl i => exact hVA i j
    | inr i => exact hVB i j
  have h := hasNMF_of_factorization (A := A + B)
    (Matrix.fromCols UA UB) (Matrix.fromRows VA VB) hU hV (by
      rw [Matrix.fromCols_mul_fromRows, hA, hB])
  simpa only [Fintype.card_sum, Fintype.card_fin] using h

theorem EntryNonneg.smul {A : Matrix m n ℝ} (hA : EntryNonneg A)
    {c : ℝ} (hc : 0 ≤ c) : EntryNonneg (c • A) :=
  fun i j => mul_nonneg hc (hA i j)

theorem HasNMF.smul {A : Matrix m n ℝ} {k : ℕ} (h : HasNMF A k)
    {c : ℝ} (hc : 0 ≤ c) : HasNMF (c • A) k := by
  obtain ⟨U, V, hU, hV, hUV⟩ := h
  refine ⟨c • U, V, hU.smul hc, hV, ?_⟩
  rw [Matrix.smul_mul, hUV]

end MatCKronecker
