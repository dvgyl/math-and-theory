import SixC55S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber55_coefficients : coeffsNonneg SixC55S4OutputPolynomial = true := by decide +kernel
theorem chamber55_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC55S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 55) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 2, 1, 5, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC55S4_eval, SixC55S3_eval, SixC55S2_eval, SixC55S1_eval, SixC55S0_eval]
theorem chamber55_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 55) z)) rawDense := by
  rw [← chamber55_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber55_coefficients
#print axioms chamber55_raw_nonneg
end SixCertificates
