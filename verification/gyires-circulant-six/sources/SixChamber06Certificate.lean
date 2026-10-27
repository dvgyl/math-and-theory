import SixC06S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber6_coefficients : coeffsNonneg SixC06S4OutputPolynomial = true := by decide +kernel
theorem chamber6_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC06S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 6) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 3, 2, 4, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC06S4_eval, SixC06S3_eval, SixC06S2_eval, SixC06S1_eval, SixC06S0_eval]
theorem chamber6_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 6) z)) rawDense := by
  rw [← chamber6_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber6_coefficients
#print axioms chamber6_raw_nonneg
end SixCertificates
