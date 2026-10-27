import SixC36S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC36S2_cofactors : ∀ p ∈ SixC36S2InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC36S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC36S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 4))) SixC36S1OutputPolynomial := by
  change _ = eval _ SixC36S2InputPolynomial
  rw [SixC36S2Output_eval, SixC36S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 4 (by decide) SixC36S2InputSlices SixC36S2_cofactors
end SixCertificates
