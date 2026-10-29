import SixC45S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC45S1_cofactors : ∀ p ∈ SixC45S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC45S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC45S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) SixC45S0OutputPolynomial := by
  change _ = eval _ SixC45S1InputPolynomial
  rw [SixC45S1Output_eval, SixC45S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC45S1InputSlices SixC45S1_cofactors
end SixCertificates
