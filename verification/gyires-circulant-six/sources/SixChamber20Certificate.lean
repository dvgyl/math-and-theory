import SixC20S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber20_coefficients : coeffsNonneg SixC20S4OutputPolynomial = true := by decide +kernel
theorem chamber20_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC20S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 20) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 5, 3, 2, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC20S4_eval, SixC20S3_eval, SixC20S2_eval, SixC20S1_eval, SixC20S0_eval]
theorem chamber20_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 20) z)) rawDense := by
  rw [← chamber20_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber20_coefficients
#print axioms chamber20_raw_nonneg
end SixCertificates
