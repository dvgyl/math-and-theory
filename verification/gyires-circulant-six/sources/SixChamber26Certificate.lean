import SixC26S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber26_coefficients : coeffsNonneg SixC26S4OutputPolynomial = true := by decide +kernel
theorem chamber26_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC26S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 26) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 1, 4, 3, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC26S4_eval, SixC26S3_eval, SixC26S2_eval, SixC26S1_eval, SixC26S0_eval]
theorem chamber26_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 26) z)) rawDense := by
  rw [← chamber26_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber26_coefficients
#print axioms chamber26_raw_nonneg
end SixCertificates
