import SixC33S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber33_coefficients : coeffsNonneg SixC33S4OutputPolynomial = true := by decide +kernel
theorem chamber33_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC33S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 33) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 2, 3, 4, 5, 1] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC33S4_eval, SixC33S3_eval, SixC33S2_eval, SixC33S1_eval, SixC33S0_eval]
theorem chamber33_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 33) z)) rawDense := by
  rw [← chamber33_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber33_coefficients
#print axioms chamber33_raw_nonneg
end SixCertificates
