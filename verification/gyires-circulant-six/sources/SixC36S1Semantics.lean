import SixC36S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC36S1_cofactors : ∀ p ∈ SixC36S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC36S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC36S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) SixC36S0OutputPolynomial := by
  change _ = eval _ SixC36S1InputPolynomial
  rw [SixC36S1Output_eval, SixC36S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC36S1InputSlices SixC36S1_cofactors
end SixCertificates
