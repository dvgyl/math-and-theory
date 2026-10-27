import SixC05S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC05S0_cofactors : ∀ p ∈ SixC05S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC05S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC05S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) rawDense := by
  change _ = eval _ SixC05S0InputPolynomial
  rw [SixC05S0Output_eval, SixC05S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC05S0InputSlices SixC05S0_cofactors
end SixCertificates
