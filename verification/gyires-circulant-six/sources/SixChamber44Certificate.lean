import SixC44S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber44_coefficients : coeffsNonneg SixC44S4OutputPolynomial = true := by decide +kernel
theorem chamber44_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC44S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 44) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 5, 3, 1, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC44S4_eval, SixC44S3_eval, SixC44S2_eval, SixC44S1_eval, SixC44S0_eval]
theorem chamber44_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 44) z)) rawDense := by
  rw [← chamber44_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber44_coefficients
#print axioms chamber44_raw_nonneg
end SixCertificates
