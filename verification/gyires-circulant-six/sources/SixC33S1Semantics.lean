import SixC33S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC33S1_cofactors : ∀ p ∈ SixC33S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC33S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC33S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) SixC33S0OutputPolynomial := by
  change _ = eval _ SixC33S1InputPolynomial
  rw [SixC33S1Output_eval, SixC33S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC33S1InputSlices SixC33S1_cofactors
end SixCertificates
