import SixC16S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber16_coefficients : coeffsNonneg SixC16S4OutputPolynomial = true := by decide +kernel
theorem chamber16_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC16S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 16) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 4, 5, 2, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC16S4_eval, SixC16S3_eval, SixC16S2_eval, SixC16S1_eval, SixC16S0_eval]
theorem chamber16_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 16) z)) rawDense := by
  rw [← chamber16_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber16_coefficients
#print axioms chamber16_raw_nonneg
end SixCertificates
