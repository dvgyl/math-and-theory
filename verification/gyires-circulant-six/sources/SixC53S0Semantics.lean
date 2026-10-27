import SixC53S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC53S0_cofactors : ∀ p ∈ SixC53S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC53S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC53S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 4))) rawDense := by
  change _ = eval _ SixC53S0InputPolynomial
  rw [SixC53S0Output_eval, SixC53S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 4 (by decide) SixC53S0InputSlices SixC53S0_cofactors
end SixCertificates
