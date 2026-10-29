import SixC54S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber54_coefficients : coeffsNonneg SixC54S4OutputPolynomial = true := by decide +kernel
theorem chamber54_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC54S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 54) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 2, 1, 4, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC54S4_eval, SixC54S3_eval, SixC54S2_eval, SixC54S1_eval, SixC54S0_eval]
theorem chamber54_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 54) z)) rawDense := by
  rw [← chamber54_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber54_coefficients
#print axioms chamber54_raw_nonneg
end SixCertificates
