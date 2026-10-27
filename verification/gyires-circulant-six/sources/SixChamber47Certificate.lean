import SixC47S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber47_coefficients : coeffsNonneg SixC47S4OutputPolynomial = true := by decide +kernel
theorem chamber47_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC47S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 47) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 5, 4, 3, 1] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC47S4_eval, SixC47S3_eval, SixC47S2_eval, SixC47S1_eval, SixC47S0_eval]
theorem chamber47_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 47) z)) rawDense := by
  rw [← chamber47_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber47_coefficients
#print axioms chamber47_raw_nonneg
end SixCertificates
