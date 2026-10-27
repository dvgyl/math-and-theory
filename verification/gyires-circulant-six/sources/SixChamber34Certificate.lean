import SixC34S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber34_coefficients : coeffsNonneg SixC34S4OutputPolynomial = true := by decide +kernel
theorem chamber34_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC34S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 34) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 3, 5, 1, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC34S4_eval, SixC34S3_eval, SixC34S2_eval, SixC34S1_eval, SixC34S0_eval]
theorem chamber34_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 34) z)) rawDense := by
  rw [← chamber34_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber34_coefficients
#print axioms chamber34_raw_nonneg
end SixCertificates
