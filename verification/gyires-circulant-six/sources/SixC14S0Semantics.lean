import SixC14S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC14S0_cofactors : ∀ p ∈ SixC14S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC14S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC14S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) rawDense := by
  change _ = eval _ SixC14S0InputPolynomial
  rw [SixC14S0Output_eval, SixC14S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC14S0InputSlices SixC14S0_cofactors
end SixCertificates
