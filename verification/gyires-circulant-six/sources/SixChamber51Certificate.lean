import SixC51S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber51_coefficients : coeffsNonneg SixC51S4OutputPolynomial = true := by decide +kernel
theorem chamber51_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC51S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 51) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 1, 4, 5, 2] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC51S4_eval, SixC51S3_eval, SixC51S2_eval, SixC51S1_eval, SixC51S0_eval]
theorem chamber51_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 51) z)) rawDense := by
  rw [← chamber51_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber51_coefficients
#print axioms chamber51_raw_nonneg
end SixCertificates
