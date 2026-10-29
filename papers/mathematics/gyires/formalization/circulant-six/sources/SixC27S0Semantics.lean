import SixC27S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC27S0_cofactors : ∀ p ∈ SixC27S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC27S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC27S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) rawDense := by
  change _ = eval _ SixC27S0InputPolynomial
  rw [SixC27S0Output_eval, SixC27S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC27S0InputSlices SixC27S0_cofactors
end SixCertificates
