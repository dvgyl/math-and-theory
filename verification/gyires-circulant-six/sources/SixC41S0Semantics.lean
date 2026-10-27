import SixC41S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC41S0_cofactors : ∀ p ∈ SixC41S0InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC41S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC41S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) rawDense := by
  change _ = eval _ SixC41S0InputPolynomial
  rw [SixC41S0Output_eval, SixC41S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC41S0InputSlices SixC41S0_cofactors
end SixCertificates
