import SixC51S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC51S0_cofactors : ∀ p ∈ SixC51S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC51S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC51S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 5))) rawDense := by
  change _ = eval _ SixC51S0InputPolynomial
  rw [SixC51S0Output_eval, SixC51S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 5 (by decide) SixC51S0InputSlices SixC51S0_cofactors
end SixCertificates
