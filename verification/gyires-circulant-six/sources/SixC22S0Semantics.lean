import SixC22S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC22S0_cofactors : ∀ p ∈ SixC22S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC22S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC22S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) rawDense := by
  change _ = eval _ SixC22S0InputPolynomial
  rw [SixC22S0Output_eval, SixC22S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC22S0InputSlices SixC22S0_cofactors
end SixCertificates
