import SixC43S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC43S1_cofactors : ∀ p ∈ SixC43S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC43S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC43S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC43S0OutputPolynomial := by
  change _ = eval _ SixC43S1InputPolynomial
  rw [SixC43S1Output_eval, SixC43S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC43S1InputSlices SixC43S1_cofactors
end SixCertificates
