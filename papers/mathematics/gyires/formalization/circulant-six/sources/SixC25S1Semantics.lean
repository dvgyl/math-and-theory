import SixC25S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC25S1_cofactors : ∀ p ∈ SixC25S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC25S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC25S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) SixC25S0OutputPolynomial := by
  change _ = eval _ SixC25S1InputPolynomial
  rw [SixC25S1Output_eval, SixC25S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC25S1InputSlices SixC25S1_cofactors
end SixCertificates
