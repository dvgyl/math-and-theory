import SixC56S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC56S0_cofactors : ∀ p ∈ SixC56S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC56S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC56S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) rawDense := by
  change _ = eval _ SixC56S0InputPolynomial
  rw [SixC56S0Output_eval, SixC56S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC56S0InputSlices SixC56S0_cofactors
end SixCertificates
