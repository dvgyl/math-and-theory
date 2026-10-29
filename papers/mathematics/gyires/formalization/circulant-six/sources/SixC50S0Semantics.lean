import SixC50S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC50S0_cofactors : ∀ p ∈ SixC50S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC50S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC50S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) rawDense := by
  change _ = eval _ SixC50S0InputPolynomial
  rw [SixC50S0Output_eval, SixC50S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC50S0InputSlices SixC50S0_cofactors
end SixCertificates
