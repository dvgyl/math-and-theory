import SixC59S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC59S2_cofactors : ∀ p ∈ SixC59S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC59S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC59S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC59S1OutputPolynomial := by
  change _ = eval _ SixC59S2InputPolynomial
  rw [SixC59S2Output_eval, SixC59S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC59S2InputSlices SixC59S2_cofactors
end SixCertificates
