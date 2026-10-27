import SixC55S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC55S1_cofactors : ∀ p ∈ SixC55S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC55S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC55S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC55S0OutputPolynomial := by
  change _ = eval _ SixC55S1InputPolynomial
  rw [SixC55S1Output_eval, SixC55S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC55S1InputSlices SixC55S1_cofactors
end SixCertificates
