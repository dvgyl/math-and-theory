import SixC21S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC21S0_cofactors : ∀ p ∈ SixC21S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC21S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC21S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 4))) rawDense := by
  change _ = eval _ SixC21S0InputPolynomial
  rw [SixC21S0Output_eval, SixC21S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 4 (by decide) SixC21S0InputSlices SixC21S0_cofactors
end SixCertificates
