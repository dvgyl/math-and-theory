module

public import MatCKronecker.NonnegativeRank

@[expose] public section

namespace MatCKronecker

open Matrix

variable {m n p q : Type*}

theorem EntryNonneg.fromBlocks {A : Matrix m n ℝ} {B : Matrix m q ℝ}
    {C : Matrix p n ℝ} {D : Matrix p q ℝ}
    (hA : EntryNonneg A) (hB : EntryNonneg B)
    (hC : EntryNonneg C) (hD : EntryNonneg D) :
    EntryNonneg (Matrix.fromBlocks A B C D) := by
  intro i j
  cases i with
  | inl i => cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  | inr i => cases j with
    | inl j => exact hC i j
    | inr j => exact hD i j

theorem EntryNonneg.blockDiag {A : Matrix m n ℝ} {B : Matrix p q ℝ}
    (hA : EntryNonneg A) (hB : EntryNonneg B) :
    EntryNonneg (Matrix.fromBlocks A 0 0 B) :=
  hA.fromBlocks (fun _ _ => le_rfl) (fun _ _ => le_rfl) hB

theorem HasNMF.blockDiag {A : Matrix m n ℝ} {B : Matrix p q ℝ} {a b : ℕ}
    (hA : HasNMF A a) (hB : HasNMF B b) :
    HasNMF (Matrix.fromBlocks A 0 0 B) (a + b) := by
  obtain ⟨UA, VA, hUA, hVA, hA⟩ := hA
  obtain ⟨UB, VB, hUB, hVB, hB⟩ := hB
  have h := hasNMF_of_factorization (A := Matrix.fromBlocks A 0 0 B)
    (Matrix.fromBlocks UA 0 0 UB) (Matrix.fromBlocks VA 0 0 VB)
    (hUA.blockDiag hUB) (hVA.blockDiag hVB) (by
      simp [Matrix.fromBlocks_multiply, hA, hB])
  simpa only [Fintype.card_sum, Fintype.card_fin] using h

/-- Every nonnegative factorization of a block diagonal matrix splits its
factor indices between the two blocks. Zero factors may be assigned to the
second block. This proves the lower bound without assuming minimal factors. -/
theorem HasNMF.blockDiag_lower {A : Matrix m n ℝ} {B : Matrix p q ℝ} {k : ℕ}
    (h : HasNMF (Matrix.fromBlocks A 0 0 B) k) :
    nnrank A + nnrank B ≤ k := by
  classical
  obtain ⟨U, V, hU, hV, hUV⟩ := h
  let active : Fin k → Prop := fun t => ∃ i : m, U (Sum.inl i) t ≠ 0
  have zeroRight (t : Fin k) (ht : active t) (j : q) : V t (Sum.inr j) = 0 := by
    obtain ⟨i, hi⟩ := ht
    have hs : ∑ s : Fin k, U (Sum.inl i) s * V s (Sum.inr j) = 0 := by
      simpa [Matrix.mul_apply] using congrArg (fun M => M (Sum.inl i) (Sum.inr j)) hUV
    have hz : U (Sum.inl i) t * V t (Sum.inr j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ => mul_nonneg (hU (Sum.inl i) s) (hV s (Sum.inr j)))).mp hs t
          (Finset.mem_univ t)
    exact (mul_eq_zero.mp hz).resolve_left hi
  have zeroLeft (t : Fin k) (ht : ¬active t) (i : m) : U (Sum.inl i) t = 0 := by
    by_contra hz
    exact ht ⟨i, hz⟩
  let UA : Matrix m {t : Fin k // active t} ℝ := fun i t => U (Sum.inl i) t
  let VA : Matrix {t : Fin k // active t} n ℝ := fun t j => V t (Sum.inl j)
  let UB : Matrix p {t : Fin k // ¬active t} ℝ := fun i t => U (Sum.inr i) t
  let VB : Matrix {t : Fin k // ¬active t} q ℝ := fun t j => V t (Sum.inr j)
  have hA : UA * VA = A := by
    ext i j
    rw [Matrix.mul_apply]
    have hzero : ∑ t : {t : Fin k // ¬active t},
        U (Sum.inl i) t * V t (Sum.inl j) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [zeroLeft t t.property i, zero_mul]
    have hfull : ∑ t : Fin k, U (Sum.inl i) t * V t (Sum.inl j) = A i j := by
      simpa [Matrix.mul_apply] using congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hUV
    have hs := (Fintype.sum_subtype_add_sum_subtype active
      (fun t => U (Sum.inl i) t * V t (Sum.inl j))).trans hfull
    simpa only [Matrix.mul_apply, UA, VA, hzero, add_zero] using hs
  have hB : UB * VB = B := by
    ext i j
    rw [Matrix.mul_apply]
    have hzero : ∑ t : {t : Fin k // active t},
        U (Sum.inr i) t * V t (Sum.inr j) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [zeroRight t t.property j, mul_zero]
    have hfull : ∑ t : Fin k, U (Sum.inr i) t * V t (Sum.inr j) = B i j := by
      simpa [Matrix.mul_apply] using congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hUV
    have hs := (Fintype.sum_subtype_add_sum_subtype active
      (fun t => U (Sum.inr i) t * V t (Sum.inr j))).trans hfull
    simpa only [Matrix.mul_apply, UB, VB, hzero, zero_add] using hs
  have hArank : nnrank A ≤ Fintype.card {t : Fin k // active t} :=
    nnrank_le_of_hasNMF (hasNMF_of_factorization UA VA
      (fun i t => hU (Sum.inl i) t) (fun t j => hV t (Sum.inl j)) hA)
  have hBrank : nnrank B ≤ Fintype.card {t : Fin k // ¬active t} :=
    nnrank_le_of_hasNMF (hasNMF_of_factorization UB VB
      (fun i t => hU (Sum.inr i) t) (fun t j => hV t (Sum.inr j)) hB)
  have hcard : Fintype.card {t : Fin k // active t} +
      Fintype.card {t : Fin k // ¬active t} = k := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (Equiv.sumCompl active)
  exact (Nat.add_le_add hArank hBrank).trans_eq hcard

theorem nnrank_fromBlocks [Fintype n] [Fintype q]
    {A : Matrix m n ℝ} {B : Matrix p q ℝ}
    (hA : EntryNonneg A) (hB : EntryNonneg B) :
    nnrank (Matrix.fromBlocks A 0 0 B) = nnrank A + nnrank B := by
  apply le_antisymm
  · exact nnrank_le_of_hasNMF ((hasNMF_nnrank hA).blockDiag (hasNMF_nnrank hB))
  · exact (hasNMF_nnrank (hA.blockDiag hB)).blockDiag_lower

end MatCKronecker
