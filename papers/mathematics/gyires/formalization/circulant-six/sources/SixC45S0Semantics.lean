import SixC45S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC45S0_cofactors : ∀ p ∈ SixC45S0InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC45S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC45S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 4))) rawDense := by
  change _ = eval _ SixC45S0InputPolynomial
  rw [SixC45S0Output_eval, SixC45S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 4 (by decide) SixC45S0InputSlices SixC45S0_cofactors
end SixCertificates
