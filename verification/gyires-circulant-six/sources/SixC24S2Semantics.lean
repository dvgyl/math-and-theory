import SixC24S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC24S2_cofactors : ∀ p ∈ SixC24S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC24S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC24S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) SixC24S1OutputPolynomial := by
  change _ = eval _ SixC24S2InputPolynomial
  rw [SixC24S2Output_eval, SixC24S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC24S2InputSlices SixC24S2_cofactors
end SixCertificates
