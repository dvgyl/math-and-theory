import SixC26S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC26S1_cofactors : ∀ p ∈ SixC26S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC26S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC26S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) SixC26S0OutputPolynomial := by
  change _ = eval _ SixC26S1InputPolynomial
  rw [SixC26S1Output_eval, SixC26S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC26S1InputSlices SixC26S1_cofactors
end SixCertificates
