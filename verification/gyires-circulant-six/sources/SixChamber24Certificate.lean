import SixC24S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber24_coefficients : coeffsNonneg SixC24S4OutputPolynomial = true := by decide +kernel
theorem chamber24_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC24S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 24) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 1, 3, 4, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC24S4_eval, SixC24S3_eval, SixC24S2_eval, SixC24S1_eval, SixC24S0_eval]
theorem chamber24_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 24) z)) rawDense := by
  rw [← chamber24_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber24_coefficients
#print axioms chamber24_raw_nonneg
end SixCertificates
