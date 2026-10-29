import BivariateCoefficients

noncomputable section
namespace PowerRank

theorem biIndex_eta (s : Fin 2 →₀ ℕ) : biIndex (s 0) (s 1) = s := by
  ext i
  fin_cases i <;> simp [biIndex]

/-- Reconstruction on an explicitly bounded two-variable coefficient grid. -/
theorem bivariate_grid_coeff {R : Type*} [CommSemiring R]
    (p : MvPolynomial (Fin 2) R) (J C j c : ℕ) :
    (∑ a ∈ Finset.range (J + 1), ∑ b ∈ Finset.range (C + 1),
      MvPolynomial.monomial (biIndex a b) (p.coeff (biIndex a b))).coeff (biIndex j c) =
      if j ≤ J ∧ c ≤ C then p.coeff (biIndex j c) else 0 := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, biIndex_eq_iff]
  split_ifs with hvalid
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single c]
      · simp
      · intro b hb hne
        simp [hne]
      · intro hnot
        exfalso
        apply hnot
        simp only [Finset.mem_range]
        omega
    · intro a ha haj
      apply Finset.sum_eq_zero
      intro b hb
      simp [haj]
    · intro hnot
      exfalso
      apply hnot
      simp only [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    apply ite_eq_right
    intro heq
    apply hvalid
    have haJ : a ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbC : b ≤ C := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    omega

theorem bivariate_reconstruct {R : Type*} [CommSemiring R]
    (p : MvPolynomial (Fin 2) R) (J C : ℕ)
    (hbound : ∀ s, p.coeff s ≠ 0 → s 0 ≤ J ∧ s 1 ≤ C) :
    p = ∑ a ∈ Finset.range (J + 1), ∑ b ∈ Finset.range (C + 1),
      MvPolynomial.monomial (biIndex a b) (p.coeff (biIndex a b)) := by
  classical
  apply MvPolynomial.ext
  intro s
  rw [← biIndex_eta s, bivariate_grid_coeff]
  by_cases hb : s 0 ≤ J ∧ s 1 ≤ C
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb]
    by_contra hp
    apply hb
    simpa only [biIndex_eta] using hbound _ hp

theorem actualGenerator_pow_grid (M : ℕ) :
    actualGenerator ^ M =
      ∑ j ∈ Finset.range (2 * M + 1), ∑ c ∈ Finset.range (M + 1),
        MvPolynomial.monomial (biIndex j c) ((actualGenerator ^ M).coeff (biIndex j c)) := by
  apply bivariate_reconstruct
  intro s hs
  have hb : s 1 ≤ M ∧ 2 * s 1 ≤ s 0 ∧ s 0 ≤ M + s 1 := by
    by_contra hb
    apply hs
    rw [← biIndex_eta s, actualGenerator, trinomialGenerator_pow_coeff,
      ite_eq_right hb]
  exact ⟨by omega, hb.1⟩

open Polynomial

theorem signed_binomial_natDegree_le (N r : ℕ) (hr : r ≤ N) :
    (((1 + X : ℚ[X]) ^ (N - r)) * (1 - X) ^ r).natDegree ≤ N := by
  have hA : (1 + X : ℚ[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (by simp)
  have hB : (1 - X : ℚ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  apply natDegree_mul_le.trans
  rw [natDegree_pow, natDegree_pow]
  calc
    _ ≤ (N - r) * 1 + r * 1 := Nat.add_le_add
      (Nat.mul_le_mul_left _ hA) (Nat.mul_le_mul_left _ hB)
    _ = N := by omega

theorem actualGenerator_coeff_natDegree_le (M j c : ℕ) :
    ((actualGenerator ^ M).coeff (biIndex j c)).natDegree ≤ M + j := by
  by_cases hvalid : c ≤ M ∧ 2 * c ≤ j ∧ j ≤ M + c
  · rw [actualGenerator_pow_coeff M j c hvalid.1 hvalid.2.1 hvalid.2.2]
    exact (natDegree_C_mul_le _ _).trans (signed_binomial_natDegree_le _ _ (by omega))
  · rw [actualGenerator, trinomialGenerator_pow_coeff, ite_eq_right hvalid]
    simp

end PowerRank
