import SixC12S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber12_coefficients : coeffsNonneg SixC12S4OutputPolynomial = true := by decide +kernel
theorem chamber12_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC12S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 12) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 4, 2, 3, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC12S4_eval, SixC12S3_eval, SixC12S2_eval, SixC12S1_eval, SixC12S0_eval]
theorem chamber12_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 12) z)) rawDense := by
  rw [← chamber12_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber12_coefficients
#print axioms chamber12_raw_nonneg
end SixCertificates
