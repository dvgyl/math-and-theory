import SixC35S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC35S0_cofactors : ∀ p ∈ SixC35S0InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC35S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC35S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 4))) rawDense := by
  change _ = eval _ SixC35S0InputPolynomial
  rw [SixC35S0Output_eval, SixC35S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 4 (by decide) SixC35S0InputSlices SixC35S0_cofactors
end SixCertificates
