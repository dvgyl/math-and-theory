import SixC30S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC30S2_cofactors : ∀ p ∈ SixC30S2InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC30S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC30S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) SixC30S1OutputPolynomial := by
  change _ = eval _ SixC30S2InputPolynomial
  rw [SixC30S2Output_eval, SixC30S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC30S2InputSlices SixC30S2_cofactors
end SixCertificates
