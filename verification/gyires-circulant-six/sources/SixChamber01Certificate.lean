import SixC01S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber1_coefficients : coeffsNonneg SixC01S4OutputPolynomial = true := by decide +kernel
theorem chamber1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC01S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 1) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 2, 3, 5, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC01S4_eval, SixC01S3_eval, SixC01S2_eval, SixC01S1_eval, SixC01S0_eval]
theorem chamber1_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 1) z)) rawDense := by
  rw [← chamber1_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber1_coefficients
#print axioms chamber1_raw_nonneg
end SixCertificates
