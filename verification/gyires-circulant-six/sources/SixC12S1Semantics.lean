import SixC12S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC12S1_cofactors : ∀ p ∈ SixC12S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC12S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC12S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) SixC12S0OutputPolynomial := by
  change _ = eval _ SixC12S1InputPolynomial
  rw [SixC12S1Output_eval, SixC12S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC12S1InputSlices SixC12S1_cofactors
end SixCertificates
