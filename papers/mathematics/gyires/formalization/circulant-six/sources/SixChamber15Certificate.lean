import SixC15S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber15_coefficients : coeffsNonneg SixC15S4OutputPolynomial = true := by decide +kernel
theorem chamber15_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC15S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 15) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 4, 3, 5, 2] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC15S4_eval, SixC15S3_eval, SixC15S2_eval, SixC15S1_eval, SixC15S0_eval]
theorem chamber15_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 15) z)) rawDense := by
  rw [← chamber15_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber15_coefficients
#print axioms chamber15_raw_nonneg
end SixCertificates
