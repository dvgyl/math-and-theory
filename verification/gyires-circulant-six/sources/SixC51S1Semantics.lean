import SixC51S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC51S1_cofactors : ∀ p ∈ SixC51S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC51S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC51S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) SixC51S0OutputPolynomial := by
  change _ = eval _ SixC51S1InputPolynomial
  rw [SixC51S1Output_eval, SixC51S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC51S1InputSlices SixC51S1_cofactors
end SixCertificates
