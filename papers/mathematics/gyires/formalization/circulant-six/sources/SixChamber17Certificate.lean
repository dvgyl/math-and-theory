import SixC17S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber17_coefficients : coeffsNonneg SixC17S4OutputPolynomial = true := by decide +kernel
theorem chamber17_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC17S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 17) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 4, 5, 3, 2] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC17S4_eval, SixC17S3_eval, SixC17S2_eval, SixC17S1_eval, SixC17S0_eval]
theorem chamber17_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 17) z)) rawDense := by
  rw [← chamber17_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber17_coefficients
#print axioms chamber17_raw_nonneg
end SixCertificates
