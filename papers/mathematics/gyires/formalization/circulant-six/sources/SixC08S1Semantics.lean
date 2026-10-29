import SixC08S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC08S1_cofactors : ∀ p ∈ SixC08S1InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC08S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC08S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 4))) SixC08S0OutputPolynomial := by
  change _ = eval _ SixC08S1InputPolynomial
  rw [SixC08S1Output_eval, SixC08S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 4 (by decide) SixC08S1InputSlices SixC08S1_cofactors
end SixCertificates
