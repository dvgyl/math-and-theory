import SixC46S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC46S0_cofactors : ∀ p ∈ SixC46S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC46S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC46S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) rawDense := by
  change _ = eval _ SixC46S0InputPolynomial
  rw [SixC46S0Output_eval, SixC46S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC46S0InputSlices SixC46S0_cofactors
end SixCertificates
