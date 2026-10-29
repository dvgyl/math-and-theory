import SixC59S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber59_coefficients : coeffsNonneg SixC59S4OutputPolynomial = true := by decide +kernel
theorem chamber59_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC59S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 59) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 2, 5, 4, 1] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC59S4_eval, SixC59S3_eval, SixC59S2_eval, SixC59S1_eval, SixC59S0_eval]
theorem chamber59_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 59) z)) rawDense := by
  rw [← chamber59_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber59_coefficients
#print axioms chamber59_raw_nonneg
end SixCertificates
