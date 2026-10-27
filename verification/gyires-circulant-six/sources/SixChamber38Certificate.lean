import SixC38S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber38_coefficients : coeffsNonneg SixC38S4OutputPolynomial = true := by decide +kernel
theorem chamber38_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC38S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 38) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 4, 3, 1, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC38S4_eval, SixC38S3_eval, SixC38S2_eval, SixC38S1_eval, SixC38S0_eval]
theorem chamber38_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 38) z)) rawDense := by
  rw [← chamber38_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber38_coefficients
#print axioms chamber38_raw_nonneg
end SixCertificates
