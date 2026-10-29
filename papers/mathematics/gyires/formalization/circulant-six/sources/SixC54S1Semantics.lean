import SixC54S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC54S1_cofactors : ∀ p ∈ SixC54S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC54S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC54S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC54S0OutputPolynomial := by
  change _ = eval _ SixC54S1InputPolynomial
  rw [SixC54S1Output_eval, SixC54S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC54S1InputSlices SixC54S1_cofactors
end SixCertificates
