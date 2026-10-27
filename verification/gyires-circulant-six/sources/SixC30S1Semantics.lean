import SixC30S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC30S1_cofactors : ∀ p ∈ SixC30S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC30S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC30S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC30S0OutputPolynomial := by
  change _ = eval _ SixC30S1InputPolynomial
  rw [SixC30S1Output_eval, SixC30S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC30S1InputSlices SixC30S1_cofactors
end SixCertificates
