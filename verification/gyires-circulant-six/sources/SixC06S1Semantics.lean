import SixC06S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC06S1_cofactors : ∀ p ∈ SixC06S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC06S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC06S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC06S0OutputPolynomial := by
  change _ = eval _ SixC06S1InputPolynomial
  rw [SixC06S1Output_eval, SixC06S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC06S1InputSlices SixC06S1_cofactors
end SixCertificates
