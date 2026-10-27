import SixC15S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC15S1_cofactors : ∀ p ∈ SixC15S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC15S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC15S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) SixC15S0OutputPolynomial := by
  change _ = eval _ SixC15S1InputPolynomial
  rw [SixC15S1Output_eval, SixC15S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC15S1InputSlices SixC15S1_cofactors
end SixCertificates
