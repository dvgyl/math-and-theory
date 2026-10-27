import SixC05S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC05S1_cofactors : ∀ p ∈ SixC05S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC05S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC05S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) SixC05S0OutputPolynomial := by
  change _ = eval _ SixC05S1InputPolynomial
  rw [SixC05S1Output_eval, SixC05S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC05S1InputSlices SixC05S1_cofactors
end SixCertificates
