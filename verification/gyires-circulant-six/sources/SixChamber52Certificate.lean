import SixC52S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber52_coefficients : coeffsNonneg SixC52S4OutputPolynomial = true := by decide +kernel
theorem chamber52_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC52S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 52) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 1, 5, 2, 4] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC52S4_eval, SixC52S3_eval, SixC52S2_eval, SixC52S1_eval, SixC52S0_eval]
theorem chamber52_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 52) z)) rawDense := by
  rw [← chamber52_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber52_coefficients
#print axioms chamber52_raw_nonneg
end SixCertificates
