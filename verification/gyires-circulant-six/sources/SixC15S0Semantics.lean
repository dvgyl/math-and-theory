import SixC15S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC15S0_cofactors : ∀ p ∈ SixC15S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC15S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC15S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 5))) rawDense := by
  change _ = eval _ SixC15S0InputPolynomial
  rw [SixC15S0Output_eval, SixC15S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 5 (by decide) SixC15S0InputSlices SixC15S0_cofactors
end SixCertificates
