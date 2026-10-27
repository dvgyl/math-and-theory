import SixC23S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber23_coefficients : coeffsNonneg SixC23S4OutputPolynomial = true := by decide +kernel
theorem chamber23_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC23S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 23) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 5, 4, 3, 2] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC23S4_eval, SixC23S3_eval, SixC23S2_eval, SixC23S1_eval, SixC23S0_eval]
theorem chamber23_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 23) z)) rawDense := by
  rw [← chamber23_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber23_coefficients
#print axioms chamber23_raw_nonneg
end SixCertificates
