import SixC23S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC23S0_cofactors : ∀ p ∈ SixC23S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC23S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC23S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) rawDense := by
  change _ = eval _ SixC23S0InputPolynomial
  rw [SixC23S0Output_eval, SixC23S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC23S0InputSlices SixC23S0_cofactors
end SixCertificates
