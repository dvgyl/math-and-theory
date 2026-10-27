import SixC37S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber37_coefficients : coeffsNonneg SixC37S4OutputPolynomial = true := by decide +kernel
theorem chamber37_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC37S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 37) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 4, 1, 5, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC37S4_eval, SixC37S3_eval, SixC37S2_eval, SixC37S1_eval, SixC37S0_eval]
theorem chamber37_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 37) z)) rawDense := by
  rw [← chamber37_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber37_coefficients
#print axioms chamber37_raw_nonneg
end SixCertificates
