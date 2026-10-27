import SixC09S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber9_coefficients : coeffsNonneg SixC09S4OutputPolynomial = true := by decide +kernel
theorem chamber9_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC09S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 9) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 3, 4, 5, 2] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC09S4_eval, SixC09S3_eval, SixC09S2_eval, SixC09S1_eval, SixC09S0_eval]
theorem chamber9_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 9) z)) rawDense := by
  rw [← chamber9_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber9_coefficients
#print axioms chamber9_raw_nonneg
end SixCertificates
