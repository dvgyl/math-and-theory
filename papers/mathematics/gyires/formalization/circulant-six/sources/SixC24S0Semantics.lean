import SixC24S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC24S0_cofactors : ∀ p ∈ SixC24S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC24S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC24S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) rawDense := by
  change _ = eval _ SixC24S0InputPolynomial
  rw [SixC24S0Output_eval, SixC24S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC24S0InputSlices SixC24S0_cofactors
end SixCertificates
