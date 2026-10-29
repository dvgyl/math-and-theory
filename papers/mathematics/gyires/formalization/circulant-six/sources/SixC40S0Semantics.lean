import SixC40S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC40S0_cofactors : ∀ p ∈ SixC40S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC40S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC40S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) rawDense := by
  change _ = eval _ SixC40S0InputPolynomial
  rw [SixC40S0Output_eval, SixC40S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC40S0InputSlices SixC40S0_cofactors
end SixCertificates
