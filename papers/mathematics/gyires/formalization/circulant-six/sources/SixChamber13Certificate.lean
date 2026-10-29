import SixC13S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber13_coefficients : coeffsNonneg SixC13S4OutputPolynomial = true := by decide +kernel
theorem chamber13_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC13S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 13) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 4, 2, 5, 3] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC13S4_eval, SixC13S3_eval, SixC13S2_eval, SixC13S1_eval, SixC13S0_eval]
theorem chamber13_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 13) z)) rawDense := by
  rw [← chamber13_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber13_coefficients
#print axioms chamber13_raw_nonneg
end SixCertificates
