import SixC45S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC45S2_cofactors : ∀ p ∈ SixC45S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC45S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC45S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) SixC45S1OutputPolynomial := by
  change _ = eval _ SixC45S2InputPolynomial
  rw [SixC45S2Output_eval, SixC45S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC45S2InputSlices SixC45S2_cofactors
end SixCertificates
