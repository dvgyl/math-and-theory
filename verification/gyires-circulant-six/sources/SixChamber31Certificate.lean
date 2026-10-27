import SixC31S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber31_coefficients : coeffsNonneg SixC31S4OutputPolynomial = true := by decide +kernel
theorem chamber31_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC31S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 31) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 3, 1, 5, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC31S4_eval, SixC31S3_eval, SixC31S2_eval, SixC31S1_eval, SixC31S0_eval]
theorem chamber31_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 31) z)) rawDense := by
  rw [← chamber31_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber31_coefficients
#print axioms chamber31_raw_nonneg
end SixCertificates
