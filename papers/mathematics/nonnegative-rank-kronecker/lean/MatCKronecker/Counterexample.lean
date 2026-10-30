module

public import MatCKronecker.CrossFactors
public import MatCKronecker.SeedNonnegativeRank
public import MatCKronecker.BlockRank
public import MatCKronecker.BlockKronecker

@[expose] public section

namespace MatCKronecker

open Matrix
open scoped Kronecker

noncomputable def witnessMatrix (t : ℕ) :
    Matrix (Fin 4 ⊕ Option (Fin t)) (Fin 4 ⊕ Option (Fin t)) ℝ :=
  Matrix.fromBlocks seed 0 0 (smallBlock t)

theorem smallBlock_nonneg {t : ℕ} (ht : 0 < t) : EntryNonneg (smallBlock t) :=
  nearOne_nonneg _ (crossEpsilon_pos ht).le

theorem witness_nonneg {t : ℕ} (ht : 0 < t) : EntryNonneg (witnessMatrix t) := by
  intro i j
  cases i <;> cases j <;> simp only [witnessMatrix, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact seed_nonneg _ _
  · exact le_rfl
  · exact le_rfl
  · exact smallBlock_nonneg ht _ _

theorem witness_rank {t : ℕ} (ht : 0 < t) : (witnessMatrix t).rank = t + 4 := by
  rw [witnessMatrix, rank_fromBlocks, seed_rank, smallBlock,
    rank_nearOne _ (crossEpsilon_pos ht)]
  simp
  omega

theorem witness_nnrank {t : ℕ} (ht : 0 < t) : nnrank (witnessMatrix t) = t + 5 := by
  rw [witnessMatrix, nnrank_fromBlocks seed_nonneg (smallBlock_nonneg ht),
    seed_nnrank, smallBlock, nnrank_nearOne _ (crossEpsilon_pos ht)]
  simp
  omega

theorem smallBlock_hasNMF {t : ℕ} (ht : 0 < t) : HasNMF (smallBlock t) (t + 1) := by
  have h := hasNMF_nnrank (smallBlock_nonneg ht)
  simpa [smallBlock, nnrank_nearOne _ (crossEpsilon_pos ht)] using h

theorem witness_square_hasNMF {t : ℕ} (ht : 0 < t) :
    HasNMF (witnessMatrix t ⊗ₖ witnessMatrix t) ((t + 4) ^ 2 + 9) := by
  have hAB := cross_hasNMF ht
  have hB := smallBlock_hasNMF ht
  have h := (seed_hasNMF_four.kronecker seed_hasNMF_four).blockDiag_kronecker
    hAB hAB.kronecker_swap (hB.kronecker hB)
  change HasNMF (witnessMatrix t ⊗ₖ witnessMatrix t)
    ((4 * 4 + (3 * t + 4)) + ((3 * t + 4) + (t + 1) * (t + 1))) at h
  convert h using 1; ring

theorem witness_square_nnrank_le {t : ℕ} (ht : 0 < t) :
    nnrank (witnessMatrix t ⊗ₖ witnessMatrix t) ≤ (t + 4) ^ 2 + 9 :=
  nnrank_le_of_hasNMF (witness_square_hasNMF ht)

/-- Arbitrarily large additive violations, with no asserted equality for the
nonnegative rank of the square. -/
theorem witness_unbounded_gap (k : ℕ) :
    nnrank (witnessMatrix (k + 6) ⊗ₖ witnessMatrix (k + 6)) + k <
      nnrank (witnessMatrix (k + 6)) * (witnessMatrix (k + 6)).rank := by
  have ht : 0 < k + 6 := by omega
  have h := witness_square_nnrank_le ht
  rw [witness_nnrank ht, witness_rank ht]
  nlinarith

def RationalEntries {m n : Type*} (A : Matrix m n ℝ) : Prop :=
  ∀ i j, ∃ q : ℚ, (q : ℝ) = A i j

theorem seed_rational : RationalEntries seed := by
  intro i j
  have h : seed i j = 17 ∨ seed i j = 1 := by
    fin_cases i <;> fin_cases j <;> norm_num [seed]
  rcases h with h | h
  · exact ⟨17, by norm_num [h]⟩
  · exact ⟨1, by norm_num [h]⟩

theorem crossEpsilon_rational (t : ℕ) : ∃ q : ℚ, (q : ℝ) = crossEpsilon t := by
  refine ⟨1 / (33600 * (3 * (t : ℚ)) * (3 * (t : ℚ) + 1)), ?_⟩
  push_cast
  rfl

theorem smallBlock_rational (t : ℕ) : RationalEntries (smallBlock t) := by
  intro i j
  obtain ⟨q, hq⟩ := crossEpsilon_rational t
  by_cases h : i = j
  · refine ⟨1 + q, ?_⟩
    simp [smallBlock, nearOne, h, hq]
  · refine ⟨1, ?_⟩
    simp [smallBlock, nearOne, h]

theorem witness_rational (t : ℕ) : RationalEntries (witnessMatrix t) := by
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j => exact seed_rational i j
      | inr j => exact ⟨0, by simp [witnessMatrix]⟩
  | inr i =>
      cases j with
      | inl j => exact ⟨0, by simp [witnessMatrix]⟩
      | inr j => exact smallBlock_rational t i j

noncomputable def witnessIndexEquiv (k : ℕ) :
    (Fin 4 ⊕ Option (Fin (k + 6))) ≃ Fin (k + 11) :=
  Fintype.equivFinOfCardEq (by simp; omega)

noncomputable def finiteWitness (k : ℕ) : Matrix (Fin (k + 11)) (Fin (k + 11)) ℝ :=
  (witnessMatrix (k + 6)).submatrix (witnessIndexEquiv k).symm (witnessIndexEquiv k).symm

/-- Full rational matrix statement, with the actual minimum nonnegative
factorization rank and an explicit unbounded additive deficit. -/
theorem exists_rational_counterexample_with_gap (k : ℕ) :
    ∃ C : Matrix (Fin (k + 11)) (Fin (k + 11)) ℝ,
      EntryNonneg C ∧ RationalEntries C ∧ C.rank = k + 10 ∧ nnrank C = k + 11 ∧
      nnrank (C ⊗ₖ C) ≤ (k + 10) ^ 2 + 9 ∧
      nnrank (C ⊗ₖ C) + k < nnrank C * C.rank := by
  have ht : 0 < k + 6 := by omega
  let e := (witnessIndexEquiv k).symm
  have hnonneg : EntryNonneg (finiteWitness k) :=
    fun i j => witness_nonneg ht (e i) (e j)
  have hrat : RationalEntries (finiteWitness k) :=
    fun i j => witness_rational (k + 6) (e i) (e j)
  have hrank : (finiteWitness k).rank = k + 10 := by
    rw [finiteWitness, Matrix.rank_submatrix, witness_rank ht]
  have hnnrank : nnrank (finiteWitness k) = k + 11 := by
    rw [finiteWitness, nnrank_submatrix_equiv (witness_nonneg ht), witness_nnrank ht]
  have hsquare : nnrank (finiteWitness k ⊗ₖ finiteWitness k) ≤ (k + 10) ^ 2 + 9 := by
    have h := (witness_square_hasNMF ht).submatrix (Equiv.prodCongr e e) (Equiv.prodCongr e e)
    have heq : (witnessMatrix (k + 6) ⊗ₖ witnessMatrix (k + 6)).submatrix
        (Equiv.prodCongr e e) (Equiv.prodCongr e e) = finiteWitness k ⊗ₖ finiteWitness k := by
      ext i j
      rfl
    rw [heq] at h
    have hb := nnrank_le_of_hasNMF h
    exact hb
  refine ⟨finiteWitness k, hnonneg, hrat, hrank, hnnrank, hsquare, ?_⟩
  rw [hrank, hnnrank]
  nlinarith

theorem counterexample_eleven :
    ∃ C : Matrix (Fin 11) (Fin 11) ℝ,
      EntryNonneg C ∧ RationalEntries C ∧ C.rank = 10 ∧ nnrank C = 11 ∧
      nnrank (C ⊗ₖ C) ≤ 109 ∧ nnrank (C ⊗ₖ C) < nnrank C * C.rank := by
  simpa using exists_rational_counterexample_with_gap 0

/-- Negation of the literal all-nonnegative-matrices conjecture; rectangular
inputs and real, rather than rational-only, factorizations are quantified. -/
theorem vandaele_gillis_glineur_tuyttens_conjecture_false :
    ¬ (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), EntryNonneg A →
      nnrank A * A.rank ≤ nnrank (A ⊗ₖ A)) := by
  intro h
  obtain ⟨C, hC, hrat, hrank, hnnrank, hu, hlt⟩ := counterexample_eleven
  exact (not_le_of_gt hlt) (h 11 11 C hC)

end MatCKronecker
