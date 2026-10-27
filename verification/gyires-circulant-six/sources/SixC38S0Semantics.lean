import SixC38S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC38S0_cofactors : ∀ p ∈ SixC38S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC38S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC38S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) rawDense := by
  change _ = eval _ SixC38S0InputPolynomial
  rw [SixC38S0Output_eval, SixC38S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC38S0InputSlices SixC38S0_cofactors
end SixCertificates
