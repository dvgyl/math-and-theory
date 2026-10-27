import SixC31S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC31S0_cofactors : ∀ p ∈ SixC31S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC31S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC31S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) rawDense := by
  change _ = eval _ SixC31S0InputPolynomial
  rw [SixC31S0Output_eval, SixC31S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC31S0InputSlices SixC31S0_cofactors
end SixCertificates
