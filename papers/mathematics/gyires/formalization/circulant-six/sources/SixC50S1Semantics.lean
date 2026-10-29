import SixC50S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC50S1_cofactors : ∀ p ∈ SixC50S1InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC50S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC50S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 4))) SixC50S0OutputPolynomial := by
  change _ = eval _ SixC50S1InputPolynomial
  rw [SixC50S1Output_eval, SixC50S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 4 (by decide) SixC50S1InputSlices SixC50S1_cofactors
end SixCertificates
