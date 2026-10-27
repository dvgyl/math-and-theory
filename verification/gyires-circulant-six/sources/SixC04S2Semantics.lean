import SixC04S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC04S2_cofactors : ∀ p ∈ SixC04S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC04S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC04S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC04S1OutputPolynomial := by
  change _ = eval _ SixC04S2InputPolynomial
  rw [SixC04S2Output_eval, SixC04S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC04S2InputSlices SixC04S2_cofactors
end SixCertificates
