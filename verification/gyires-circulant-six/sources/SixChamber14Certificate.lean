import SixC14S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber14_coefficients : coeffsNonneg SixC14S4OutputPolynomial = true := by decide +kernel
theorem chamber14_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC14S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 14) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 4, 3, 2, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC14S4_eval, SixC14S3_eval, SixC14S2_eval, SixC14S1_eval, SixC14S0_eval]
theorem chamber14_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 14) z)) rawDense := by
  rw [← chamber14_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber14_coefficients
#print axioms chamber14_raw_nonneg
end SixCertificates
