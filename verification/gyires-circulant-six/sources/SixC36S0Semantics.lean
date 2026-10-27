import SixC36S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC36S0_cofactors : ∀ p ∈ SixC36S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC36S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC36S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) rawDense := by
  change _ = eval _ SixC36S0InputPolynomial
  rw [SixC36S0Output_eval, SixC36S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC36S0InputSlices SixC36S0_cofactors
end SixCertificates
