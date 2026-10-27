import SixC22S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber22_coefficients : coeffsNonneg SixC22S4OutputPolynomial = true := by decide +kernel
theorem chamber22_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC22S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 22) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 5, 4, 2, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC22S4_eval, SixC22S3_eval, SixC22S2_eval, SixC22S1_eval, SixC22S0_eval]
theorem chamber22_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 22) z)) rawDense := by
  rw [← chamber22_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber22_coefficients
#print axioms chamber22_raw_nonneg
end SixCertificates
