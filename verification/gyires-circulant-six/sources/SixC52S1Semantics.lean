import SixC52S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC52S1_cofactors : ∀ p ∈ SixC52S1InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC52S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC52S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 5))) SixC52S0OutputPolynomial := by
  change _ = eval _ SixC52S1InputPolynomial
  rw [SixC52S1Output_eval, SixC52S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 5 (by decide) SixC52S1InputSlices SixC52S1_cofactors
end SixCertificates
