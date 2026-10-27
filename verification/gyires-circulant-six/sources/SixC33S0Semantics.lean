import SixC33S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC33S0_cofactors : ∀ p ∈ SixC33S0InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC33S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC33S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 5))) rawDense := by
  change _ = eval _ SixC33S0InputPolynomial
  rw [SixC33S0Output_eval, SixC33S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 5 (by decide) SixC33S0InputSlices SixC33S0_cofactors
end SixCertificates
