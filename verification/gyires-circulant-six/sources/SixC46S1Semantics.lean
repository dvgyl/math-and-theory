import SixC46S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC46S1_cofactors : ∀ p ∈ SixC46S1InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC46S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC46S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 4))) SixC46S0OutputPolynomial := by
  change _ = eval _ SixC46S1InputPolynomial
  rw [SixC46S1Output_eval, SixC46S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 4 (by decide) SixC46S1InputSlices SixC46S1_cofactors
end SixCertificates
