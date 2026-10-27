import SixC42S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber42_coefficients : coeffsNonneg SixC42S4OutputPolynomial = true := by decide +kernel
theorem chamber42_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC42S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 42) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 5, 1, 3, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC42S4_eval, SixC42S3_eval, SixC42S2_eval, SixC42S1_eval, SixC42S0_eval]
theorem chamber42_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 42) z)) rawDense := by
  rw [← chamber42_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber42_coefficients
#print axioms chamber42_raw_nonneg
end SixCertificates
