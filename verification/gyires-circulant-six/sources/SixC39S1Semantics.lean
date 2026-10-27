import SixC39S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC39S1_cofactors : ∀ p ∈ SixC39S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC39S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC39S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) SixC39S0OutputPolynomial := by
  change _ = eval _ SixC39S1InputPolynomial
  rw [SixC39S1Output_eval, SixC39S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC39S1InputSlices SixC39S1_cofactors
end SixCertificates
