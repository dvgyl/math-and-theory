import SixC10S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber10_coefficients : coeffsNonneg SixC10S4OutputPolynomial = true := by decide +kernel
theorem chamber10_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC10S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 10) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 3, 5, 2, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC10S4_eval, SixC10S3_eval, SixC10S2_eval, SixC10S1_eval, SixC10S0_eval]
theorem chamber10_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 10) z)) rawDense := by
  rw [← chamber10_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber10_coefficients
#print axioms chamber10_raw_nonneg
end SixCertificates
