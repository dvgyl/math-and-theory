module
public import MathAndTheory.Mathematics.QPermanent.GeneralBlock
public import MathAndTheory.Mathematics.QPermanent.CoreEnumeration
public import MathAndTheory.Mathematics.QPermanent.GeneralAnalysis

@[expose] public section

namespace MathAndTheory.QPermanent

open scoped BigOperators

theorem qPermanent_family_formula (m : ℕ) (a d q : ℝ) :
    qPermanent (familyMatrix m a d) q =
      d ^ 4 + d ^ 2 * q ^ (2 * m + 1) * (1 + 2 * a ^ 2 * q ^ 2 + q ^ 4) +
        q ^ (4 * m + 4) * (a ^ 2 - q) ^ 2 := by
  rw [qPermanent_family_reduction]
  have hsum : (∑ σ : Equiv.Perm (Fin 4),
      q ^ inversionCount (liftCorePermutation m σ) *
        ∏ i : Fin 4, familyCore a d i (σ i)) = coreWeightedSum a d q (q ^ m) := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [inversionCount_liftCorePermutation, pow_add, pow_mul]
  rw [hsum, coreWeightedSum_formula]
  simp only [← pow_mul, Nat.mul_comm m 2, Nat.mul_comm m 4, pow_add]
  ring

theorem qPermanent_family_sqrt (m : ℕ) (t q : ℝ) (ht : 0 ≤ t) :
    qPermanent (familyMatrix m (Real.sqrt t) (Real.sqrt (t + 2))) q =
      familyPolynomial m t (t + 2) q := by
  rw [qPermanent_family_formula]
  rw [show (Real.sqrt (t + 2)) ^ 4 = (t + 2) ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sq_sqrt (by linarith : 0 ≤ t + 2)]]
  rw [Real.sq_sqrt ht, Real.sq_sqrt (by linarith : 0 ≤ t + 2)]
  rfl

/-- The complete general theorem concerns the genuine inversion-weighted
permanent of an actual real positive-definite matrix. -/
theorem exists_posDef_negative_qPermanent_derivative_ge_five (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      5 ≤ n ∧ A.PosDef ∧ deriv (qPermanent A) r < 0 := by
  obtain ⟨m, hm, hderiv⟩ := exists_negative_familyPolynomial_derivative hr
  have ht : 0 ≤ familyT m r := (familyT_pos m (by linarith : 0 < r)).le
  refine ⟨m + 4, familyMatrix m (Real.sqrt (familyT m r))
    (Real.sqrt (familyT m r + 2)), by omega,
    familyMatrix_sqrt_posDef m _ ht, ?_⟩
  have hfun : qPermanent (familyMatrix m (Real.sqrt (familyT m r))
      (Real.sqrt (familyT m r + 2))) =
      familyPolynomial m (familyT m r) (familyT m r + 2) := by
    funext q
    exact qPermanent_family_sqrt m _ q ht
  rwa [hfun]

theorem exists_posDef_negative_qPermanent_derivative (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef ∧ deriv (qPermanent A) r < 0 := by
  obtain ⟨n, A, _, hA, hderiv⟩ :=
    exists_posDef_negative_qPermanent_derivative_ge_five r hr
  exact ⟨n, A, hA, hderiv⟩

end MathAndTheory.QPermanent
