import SixC49S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber49_coefficients : coeffsNonneg SixC49S4OutputPolynomial = true := by decide +kernel
theorem chamber49_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC49S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 49) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 1, 2, 5, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC49S4_eval, SixC49S3_eval, SixC49S2_eval, SixC49S1_eval, SixC49S0_eval]
theorem chamber49_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 49) z)) rawDense := by
  rw [← chamber49_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber49_coefficients
#print axioms chamber49_raw_nonneg
end SixCertificates
