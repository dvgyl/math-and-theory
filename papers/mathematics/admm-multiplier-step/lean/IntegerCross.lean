import IntegerMatrix

open scoped BigOperators

namespace ADMMNearSharpCertificate

variable {ν κ : Type*} [Fintype ν]

def integerCross (a b : κ → ℤ) : Matrix κ κ ℤ :=
  fun k l => a k * b l + b k * a l

def weightedDifferences (lam : Matrix ν ν ℤ) (X : Matrix ν κ ℤ) : Matrix ν κ ℤ :=
  fun i k => ∑ j, lam i j * (X j k - X i k)

/-- The dense weighted interpolation sum factors through its exact weighted
point differences. This is an algebraic identity, with no sign assumptions. -/
theorem weighted_cross_sum (A X : Matrix ν κ ℤ) (lam : Matrix ν ν ℤ) :
    (∑ i, ∑ j, lam i j • integerCross (A i) (X j-X i)) =
      ∑ i, integerCross (A i) (weightedDifferences lam X i) := by
  ext k l
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    integerCross, Pi.sub_apply, weightedDifferences]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

#print axioms weighted_cross_sum

end ADMMNearSharpCertificate
