import SixC59S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC59S0_cofactors : ∀ p ∈ SixC59S0InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC59S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC59S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 4))) rawDense := by
  change _ = eval _ SixC59S0InputPolynomial
  rw [SixC59S0Output_eval, SixC59S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 4 (by decide) SixC59S0InputSlices SixC59S0_cofactors
end SixCertificates
