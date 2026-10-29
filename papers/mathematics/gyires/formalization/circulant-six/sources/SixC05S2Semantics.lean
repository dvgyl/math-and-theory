import SixC05S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC05S2_cofactors : ∀ p ∈ SixC05S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC05S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC05S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC05S1OutputPolynomial := by
  change _ = eval _ SixC05S2InputPolynomial
  rw [SixC05S2Output_eval, SixC05S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC05S2InputSlices SixC05S2_cofactors
end SixCertificates
