import SixC09S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC09S0_cofactors : ∀ p ∈ SixC09S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC09S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC09S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 5))) rawDense := by
  change _ = eval _ SixC09S0InputPolynomial
  rw [SixC09S0Output_eval, SixC09S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 5 (by decide) SixC09S0InputSlices SixC09S0_cofactors
end SixCertificates
