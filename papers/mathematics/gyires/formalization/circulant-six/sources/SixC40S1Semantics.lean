import SixC40S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC40S1_cofactors : ∀ p ∈ SixC40S1InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC40S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC40S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 5))) SixC40S0OutputPolynomial := by
  change _ = eval _ SixC40S1InputPolynomial
  rw [SixC40S1Output_eval, SixC40S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 5 (by decide) SixC40S1InputSlices SixC40S1_cofactors
end SixCertificates
