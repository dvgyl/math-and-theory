import SixC11S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber11_coefficients : coeffsNonneg SixC11S4OutputPolynomial = true := by decide +kernel
theorem chamber11_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC11S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 11) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 3, 5, 4, 2] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC11S4_eval, SixC11S3_eval, SixC11S2_eval, SixC11S1_eval, SixC11S0_eval]
theorem chamber11_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 11) z)) rawDense := by
  rw [← chamber11_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber11_coefficients
#print axioms chamber11_raw_nonneg
end SixCertificates
