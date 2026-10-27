import SixC28S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC28S1_cofactors : ∀ p ∈ SixC28S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC28S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC28S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) SixC28S0OutputPolynomial := by
  change _ = eval _ SixC28S1InputPolynomial
  rw [SixC28S1Output_eval, SixC28S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC28S1InputSlices SixC28S1_cofactors
end SixCertificates
