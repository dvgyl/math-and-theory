import SixC27S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC27S1_cofactors : ∀ p ∈ SixC27S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC27S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC27S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) SixC27S0OutputPolynomial := by
  change _ = eval _ SixC27S1InputPolynomial
  rw [SixC27S1Output_eval, SixC27S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC27S1InputSlices SixC27S1_cofactors
end SixCertificates
