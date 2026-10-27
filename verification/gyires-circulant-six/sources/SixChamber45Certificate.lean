import SixC45S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber45_coefficients : coeffsNonneg SixC45S4OutputPolynomial = true := by decide +kernel
theorem chamber45_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC45S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 45) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 5, 3, 4, 1] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC45S4_eval, SixC45S3_eval, SixC45S2_eval, SixC45S1_eval, SixC45S0_eval]
theorem chamber45_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 45) z)) rawDense := by
  rw [← chamber45_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber45_coefficients
#print axioms chamber45_raw_nonneg
end SixCertificates
