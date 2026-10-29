import SixC19S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber19_coefficients : coeffsNonneg SixC19S4OutputPolynomial = true := by decide +kernel
theorem chamber19_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC19S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 19) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 5, 2, 4, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC19S4_eval, SixC19S3_eval, SixC19S2_eval, SixC19S1_eval, SixC19S0_eval]
theorem chamber19_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 19) z)) rawDense := by
  rw [← chamber19_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber19_coefficients
#print axioms chamber19_raw_nonneg
end SixCertificates
