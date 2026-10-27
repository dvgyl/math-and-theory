import SixC02S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber2_coefficients : coeffsNonneg SixC02S4OutputPolynomial = true := by decide +kernel
theorem chamber2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC02S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 2) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 1, 2, 4, 3, 5] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC02S4_eval, SixC02S3_eval, SixC02S2_eval, SixC02S1_eval, SixC02S0_eval]
theorem chamber2_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 2) z)) rawDense := by
  rw [← chamber2_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber2_coefficients
#print axioms chamber2_raw_nonneg
end SixCertificates
