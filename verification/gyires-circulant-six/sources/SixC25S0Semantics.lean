import SixC25S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC25S0_cofactors : ∀ p ∈ SixC25S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC25S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC25S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) rawDense := by
  change _ = eval _ SixC25S0InputPolynomial
  rw [SixC25S0Output_eval, SixC25S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC25S0InputSlices SixC25S0_cofactors
end SixCertificates
