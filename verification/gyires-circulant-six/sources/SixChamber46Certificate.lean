import SixC46S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber46_coefficients : coeffsNonneg SixC46S4OutputPolynomial = true := by decide +kernel
theorem chamber46_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC46S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 46) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 5, 4, 1, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC46S4_eval, SixC46S3_eval, SixC46S2_eval, SixC46S1_eval, SixC46S0_eval]
theorem chamber46_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 46) z)) rawDense := by
  rw [← chamber46_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber46_coefficients
#print axioms chamber46_raw_nonneg
end SixCertificates
