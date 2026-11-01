import QPermanentResearch.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

namespace QPermanentResearch

open scoped BigOperators

theorem qPermanent_one_eq_permanent {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : qPermanent A 1 = A.permanent := by
  calc
    qPermanent A 1 = A.transpose.permanent := by
      simp [qPermanent, Matrix.permanent, Matrix.transpose_apply]
    _ = A.permanent := Matrix.permanent_transpose A

theorem qPermanent_smul {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (c q : R) :
    qPermanent (c • A) q = c ^ n * qPermanent A q := by
  classical
  unfold qPermanent
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem qPermanentDerivative_smul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c q : ℝ) :
    qPermanentDerivative (c • A) q = c ^ n * qPermanentDerivative A q := by
  classical
  unfold qPermanentDerivative
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end QPermanentResearch
