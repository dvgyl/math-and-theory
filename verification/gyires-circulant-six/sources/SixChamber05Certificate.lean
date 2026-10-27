import SixC05S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber5_coefficients : coeffsNonneg SixC05S4OutputPolynomial = true := by decide +kernel
theorem chamber5_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC05S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 5) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 2, 5, 4, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC05S4_eval, SixC05S3_eval, SixC05S2_eval, SixC05S1_eval, SixC05S0_eval]
theorem chamber5_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 5) z)) rawDense := by
  rw [← chamber5_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber5_coefficients
#print axioms chamber5_raw_nonneg
end SixCertificates
