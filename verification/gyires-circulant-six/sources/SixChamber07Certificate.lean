import SixC07S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber7_coefficients : coeffsNonneg SixC07S4OutputPolynomial = true := by decide +kernel
theorem chamber7_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC07S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 7) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 3, 2, 5, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC07S4_eval, SixC07S3_eval, SixC07S2_eval, SixC07S1_eval, SixC07S0_eval]
theorem chamber7_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 7) z)) rawDense := by
  rw [← chamber7_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber7_coefficients
#print axioms chamber7_raw_nonneg
end SixCertificates
