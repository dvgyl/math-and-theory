import SixC48S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber48_coefficients : coeffsNonneg SixC48S4OutputPolynomial = true := by decide +kernel
theorem chamber48_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC48S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 48) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 1, 2, 4, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC48S4_eval, SixC48S3_eval, SixC48S2_eval, SixC48S1_eval, SixC48S0_eval]
theorem chamber48_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 48) z)) rawDense := by
  rw [← chamber48_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber48_coefficients
#print axioms chamber48_raw_nonneg
end SixCertificates
