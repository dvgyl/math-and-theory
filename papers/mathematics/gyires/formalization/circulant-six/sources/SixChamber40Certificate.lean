import SixC40S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber40_coefficients : coeffsNonneg SixC40S4OutputPolynomial = true := by decide +kernel
theorem chamber40_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC40S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 40) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 4, 5, 1, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC40S4_eval, SixC40S3_eval, SixC40S2_eval, SixC40S1_eval, SixC40S0_eval]
theorem chamber40_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 40) z)) rawDense := by
  rw [← chamber40_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber40_coefficients
#print axioms chamber40_raw_nonneg
end SixCertificates
