import SixC20S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC20S0_cofactors : ∀ p ∈ SixC20S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC20S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC20S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) rawDense := by
  change _ = eval _ SixC20S0InputPolynomial
  rw [SixC20S0Output_eval, SixC20S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC20S0InputSlices SixC20S0_cofactors
end SixCertificates
