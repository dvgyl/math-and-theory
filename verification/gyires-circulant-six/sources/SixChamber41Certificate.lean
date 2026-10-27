import SixC41S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber41_coefficients : coeffsNonneg SixC41S4OutputPolynomial = true := by decide +kernel
theorem chamber41_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC41S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 41) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 4, 5, 3, 1] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC41S4_eval, SixC41S3_eval, SixC41S2_eval, SixC41S1_eval, SixC41S0_eval]
theorem chamber41_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 41) z)) rawDense := by
  rw [← chamber41_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber41_coefficients
#print axioms chamber41_raw_nonneg
end SixCertificates
