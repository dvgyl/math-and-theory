import IntegerCross
import GapAlgebra

open scoped BigOperators

namespace ADMMNearSharpCertificate

open ADMMBarrier ADMMNearSharp

variable {ν κ : Type*} [Fintype ν]

theorem qsum_smul_weights (X A : Matrix ν κ ℝ) (lam : Matrix ν ν ℝ) (c : ℝ) :
    qsum X A (c • lam) = c • qsum X A lam := by
  unfold qsum
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem cast_weighted_cross (A X : Matrix ν κ ℤ) (lam : Matrix ν ν ℤ) :
    castMat (∑ i, ∑ j, lam i j • integerCross (A i) (X j-X i)) =
      (-2 : ℝ) • qsum (castMat X) (castMat A) (castMat lam) := by
  simp only [castMat_sum_univ, castMat_smul, qsum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ext k l
  simp only [Matrix.smul_apply, smul_eq_mul, castMat_apply, integerCross,
    Matrix.neg_apply, symouter, Pi.sub_apply, Int.cast_add, Int.cast_mul,
    Int.cast_sub]
  ring

#print axioms cast_weighted_cross

end ADMMNearSharpCertificate
