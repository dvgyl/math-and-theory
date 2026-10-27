import SixC27S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber27_coefficients : coeffsNonneg SixC27S4OutputPolynomial = true := by decide +kernel
theorem chamber27_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC27S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 27) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 1, 4, 5, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC27S4_eval, SixC27S3_eval, SixC27S2_eval, SixC27S1_eval, SixC27S0_eval]
theorem chamber27_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 27) z)) rawDense := by
  rw [← chamber27_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber27_coefficients
#print axioms chamber27_raw_nonneg
end SixCertificates
