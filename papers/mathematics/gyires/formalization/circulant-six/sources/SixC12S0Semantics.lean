import SixC12S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC12S0_cofactors : ∀ p ∈ SixC12S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC12S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC12S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) rawDense := by
  change _ = eval _ SixC12S0InputPolynomial
  rw [SixC12S0Output_eval, SixC12S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC12S0InputSlices SixC12S0_cofactors
end SixCertificates
