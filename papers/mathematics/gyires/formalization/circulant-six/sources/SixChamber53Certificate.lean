import SixC53S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber53_coefficients : coeffsNonneg SixC53S4OutputPolynomial = true := by decide +kernel
theorem chamber53_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC53S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 53) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 1, 5, 4, 2] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC53S4_eval, SixC53S3_eval, SixC53S2_eval, SixC53S1_eval, SixC53S0_eval]
theorem chamber53_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 53) z)) rawDense := by
  rw [← chamber53_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber53_coefficients
#print axioms chamber53_raw_nonneg
end SixCertificates
