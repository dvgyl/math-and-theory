import SixC28S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber28_coefficients : coeffsNonneg SixC28S4OutputPolynomial = true := by decide +kernel
theorem chamber28_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC28S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 28) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 1, 5, 3, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC28S4_eval, SixC28S3_eval, SixC28S2_eval, SixC28S1_eval, SixC28S0_eval]
theorem chamber28_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 28) z)) rawDense := by
  rw [← chamber28_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber28_coefficients
#print axioms chamber28_raw_nonneg
end SixCertificates
