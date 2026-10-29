import SixC04S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber4_coefficients : coeffsNonneg SixC04S4OutputPolynomial = true := by decide +kernel
theorem chamber4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC04S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 4) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 2, 5, 3, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC04S4_eval, SixC04S3_eval, SixC04S2_eval, SixC04S1_eval, SixC04S0_eval]
theorem chamber4_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 4) z)) rawDense := by
  rw [← chamber4_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber4_coefficients
#print axioms chamber4_raw_nonneg
end SixCertificates
