import SixC24S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC24S1_cofactors : ∀ p ∈ SixC24S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC24S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC24S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) SixC24S0OutputPolynomial := by
  change _ = eval _ SixC24S1InputPolynomial
  rw [SixC24S1Output_eval, SixC24S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC24S1InputSlices SixC24S1_cofactors
end SixCertificates
