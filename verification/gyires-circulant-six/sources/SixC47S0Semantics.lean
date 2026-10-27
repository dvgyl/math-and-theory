import SixC47S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC47S0_cofactors : ∀ p ∈ SixC47S0InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC47S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC47S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) rawDense := by
  change _ = eval _ SixC47S0InputPolynomial
  rw [SixC47S0Output_eval, SixC47S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC47S0InputSlices SixC47S0_cofactors
end SixCertificates
