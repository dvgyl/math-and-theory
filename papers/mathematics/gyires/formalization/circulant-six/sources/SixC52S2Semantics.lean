import SixC52S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC52S2_cofactors : ∀ p ∈ SixC52S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC52S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC52S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC52S1OutputPolynomial := by
  change _ = eval _ SixC52S2InputPolynomial
  rw [SixC52S2Output_eval, SixC52S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC52S2InputSlices SixC52S2_cofactors
end SixCertificates
