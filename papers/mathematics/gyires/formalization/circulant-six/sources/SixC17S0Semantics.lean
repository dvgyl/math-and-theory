import SixC17S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC17S0_cofactors : ∀ p ∈ SixC17S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC17S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC17S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) rawDense := by
  change _ = eval _ SixC17S0InputPolynomial
  rw [SixC17S0Output_eval, SixC17S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC17S0InputSlices SixC17S0_cofactors
end SixCertificates
