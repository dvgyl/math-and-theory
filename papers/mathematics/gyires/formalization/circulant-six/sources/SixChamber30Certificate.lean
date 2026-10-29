import SixC30S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber30_coefficients : coeffsNonneg SixC30S4OutputPolynomial = true := by decide +kernel
theorem chamber30_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC30S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 30) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 3, 1, 4, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC30S4_eval, SixC30S3_eval, SixC30S2_eval, SixC30S1_eval, SixC30S0_eval]
theorem chamber30_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 30) z)) rawDense := by
  rw [← chamber30_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber30_coefficients
#print axioms chamber30_raw_nonneg
end SixCertificates
