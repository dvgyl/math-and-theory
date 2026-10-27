import SixC44S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC44S1_cofactors : ∀ p ∈ SixC44S1InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC44S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC44S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) SixC44S0OutputPolynomial := by
  change _ = eval _ SixC44S1InputPolynomial
  rw [SixC44S1Output_eval, SixC44S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC44S1InputSlices SixC44S1_cofactors
end SixCertificates
