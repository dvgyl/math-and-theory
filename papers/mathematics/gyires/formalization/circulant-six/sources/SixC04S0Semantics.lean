import SixC04S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC04S0_cofactors : ∀ p ∈ SixC04S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC04S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC04S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) rawDense := by
  change _ = eval _ SixC04S0InputPolynomial
  rw [SixC04S0Output_eval, SixC04S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC04S0InputSlices SixC04S0_cofactors
end SixCertificates
