import SixC56S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber56_coefficients : coeffsNonneg SixC56S4OutputPolynomial = true := by decide +kernel
theorem chamber56_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC56S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 56) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 2, 4, 1, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC56S4_eval, SixC56S3_eval, SixC56S2_eval, SixC56S1_eval, SixC56S0_eval]
theorem chamber56_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 56) z)) rawDense := by
  rw [← chamber56_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber56_coefficients
#print axioms chamber56_raw_nonneg
end SixCertificates
