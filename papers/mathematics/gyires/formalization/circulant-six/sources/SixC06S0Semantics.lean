import SixC06S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC06S0_cofactors : ∀ p ∈ SixC06S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC06S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC06S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) rawDense := by
  change _ = eval _ SixC06S0InputPolynomial
  rw [SixC06S0Output_eval, SixC06S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC06S0InputSlices SixC06S0_cofactors
end SixCertificates
