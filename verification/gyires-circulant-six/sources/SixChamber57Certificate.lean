import SixC57S4Semantics
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem chamber57_coefficients : coeffsNonneg SixC57S4OutputPolynomial = true := by decide +kernel
theorem chamber57_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC57S4OutputPolynomial = eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 57) z)) rawDense := by
  change _ = eval (primeEvaluation primes (prefixVector ![0, 3, 2, 4, 5, 1] z)) rawDense
  simp only [prefixVector, Matrix.cons_val]
  rw [SixC57S4_eval, SixC57S3_eval, SixC57S2_eval, SixC57S1_eval, SixC57S0_eval]
theorem chamber57_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 0 ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 57) z)) rawDense := by
  rw [← chamber57_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ chamber57_coefficients
#print axioms chamber57_raw_nonneg
end SixCertificates
