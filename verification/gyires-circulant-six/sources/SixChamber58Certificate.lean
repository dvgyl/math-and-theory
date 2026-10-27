import SixC58S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber58_coefficients : coeffsNonneg SixC58S4OutputPolynomial = true := by decide +kernel
theorem chamber58_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC58S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 58) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 2, 5, 1, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC58S4_eval, SixC58S3_eval, SixC58S2_eval, SixC58S1_eval, SixC58S0_eval]
theorem chamber58_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 58) z)) rawDense := by
  rw [← chamber58_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber58_coefficients
#print axioms chamber58_raw_nonneg
end SixCertificates
