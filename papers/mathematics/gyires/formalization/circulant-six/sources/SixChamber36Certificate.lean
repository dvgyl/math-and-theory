import SixC36S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber36_coefficients : coeffsNonneg SixC36S4OutputPolynomial = true := by decide +kernel
theorem chamber36_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC36S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 36) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 4, 1, 3, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC36S4_eval, SixC36S3_eval, SixC36S2_eval, SixC36S1_eval, SixC36S0_eval]
theorem chamber36_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 36) z)) rawDense := by
  rw [← chamber36_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber36_coefficients
#print axioms chamber36_raw_nonneg
end SixCertificates
