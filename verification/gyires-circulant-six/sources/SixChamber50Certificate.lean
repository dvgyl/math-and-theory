import SixC50S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber50_coefficients : coeffsNonneg SixC50S4OutputPolynomial = true := by decide +kernel
theorem chamber50_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC50S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 50) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 1, 4, 2, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC50S4_eval, SixC50S3_eval, SixC50S2_eval, SixC50S1_eval, SixC50S0_eval]
theorem chamber50_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 50) z)) rawDense := by
  rw [← chamber50_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber50_coefficients
#print axioms chamber50_raw_nonneg
end SixCertificates
