import SixC49S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC49S1_cofactors : ∀ p ∈ SixC49S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC49S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC49S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC49S0OutputPolynomial := by
  change _ = eval _ SixC49S1InputPolynomial
  rw [SixC49S1Output_eval, SixC49S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC49S1InputSlices SixC49S1_cofactors
end SixCertificates
