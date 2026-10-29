import SixC54S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC54S0_cofactors : ∀ p ∈ SixC54S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC54S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC54S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) rawDense := by
  change _ = eval _ SixC54S0InputPolynomial
  rw [SixC54S0Output_eval, SixC54S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC54S0InputSlices SixC54S0_cofactors
end SixCertificates
