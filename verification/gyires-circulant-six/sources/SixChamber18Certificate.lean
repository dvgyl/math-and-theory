import SixC18S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber18_coefficients : coeffsNonneg SixC18S4OutputPolynomial = true := by decide +kernel
theorem chamber18_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC18S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 18) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 5, 2, 3, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC18S4_eval, SixC18S3_eval, SixC18S2_eval, SixC18S1_eval, SixC18S0_eval]
theorem chamber18_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 18) z)) rawDense := by
  rw [← chamber18_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber18_coefficients
#print axioms chamber18_raw_nonneg
end SixCertificates
