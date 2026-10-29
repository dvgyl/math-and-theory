import SixC39S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber39_coefficients : coeffsNonneg SixC39S4OutputPolynomial = true := by decide +kernel
theorem chamber39_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC39S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 39) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 4, 3, 5, 1] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC39S4_eval, SixC39S3_eval, SixC39S2_eval, SixC39S1_eval, SixC39S0_eval]
theorem chamber39_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 39) z)) rawDense := by
  rw [← chamber39_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber39_coefficients
#print axioms chamber39_raw_nonneg
end SixCertificates
