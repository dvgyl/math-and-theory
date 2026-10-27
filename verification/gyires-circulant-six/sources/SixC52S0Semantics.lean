import SixC52S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC52S0_cofactors : ∀ p ∈ SixC52S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC52S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC52S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) rawDense := by
  change _ = eval _ SixC52S0InputPolynomial
  rw [SixC52S0Output_eval, SixC52S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC52S0InputSlices SixC52S0_cofactors
end SixCertificates
