import SixC32S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC32S0_cofactors : ∀ p ∈ SixC32S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC32S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC32S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) rawDense := by
  change _ = eval _ SixC32S0InputPolynomial
  rw [SixC32S0Output_eval, SixC32S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC32S0InputSlices SixC32S0_cofactors
end SixCertificates
