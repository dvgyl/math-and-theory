import SixC08S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber8_coefficients : coeffsNonneg SixC08S4OutputPolynomial = true := by decide +kernel
theorem chamber8_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC08S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 8) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 3, 4, 2, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC08S4_eval, SixC08S3_eval, SixC08S2_eval, SixC08S1_eval, SixC08S0_eval]
theorem chamber8_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 8) z)) rawDense := by
  rw [← chamber8_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber8_coefficients
#print axioms chamber8_raw_nonneg
end SixCertificates
