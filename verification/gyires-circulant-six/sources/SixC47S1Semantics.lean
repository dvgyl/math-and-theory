import SixC47S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC47S1_cofactors : ∀ p ∈ SixC47S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC47S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC47S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) SixC47S0OutputPolynomial := by
  change _ = eval _ SixC47S1InputPolynomial
  rw [SixC47S1Output_eval, SixC47S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC47S1InputSlices SixC47S1_cofactors
end SixCertificates
