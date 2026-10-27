import SixC29S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber29_coefficients : coeffsNonneg SixC29S4OutputPolynomial = true := by decide +kernel
theorem chamber29_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC29S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 29) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 1, 5, 4, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC29S4_eval, SixC29S3_eval, SixC29S2_eval, SixC29S1_eval, SixC29S0_eval]
theorem chamber29_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 29) z)) rawDense := by
  rw [← chamber29_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber29_coefficients
#print axioms chamber29_raw_nonneg
end SixCertificates
