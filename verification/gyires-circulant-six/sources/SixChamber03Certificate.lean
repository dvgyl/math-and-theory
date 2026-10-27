import SixC03S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber3_coefficients : coeffsNonneg SixC03S4OutputPolynomial = true := by decide +kernel
theorem chamber3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC03S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 3) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 2, 4, 5, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC03S4_eval, SixC03S3_eval, SixC03S2_eval, SixC03S1_eval, SixC03S0_eval]
theorem chamber3_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 3) z)) rawDense := by
  rw [← chamber3_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber3_coefficients
#print axioms chamber3_raw_nonneg
end SixCertificates
