import SixC42S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC42S0_cofactors : ∀ p ∈ SixC42S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC42S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC42S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) rawDense := by
  change _ = eval _ SixC42S0InputPolynomial
  rw [SixC42S0Output_eval, SixC42S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC42S0InputSlices SixC42S0_cofactors
end SixCertificates
