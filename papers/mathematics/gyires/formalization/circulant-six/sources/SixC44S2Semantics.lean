import SixC44S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC44S2_cofactors : ∀ p ∈ SixC44S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC44S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC44S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) SixC44S1OutputPolynomial := by
  change _ = eval _ SixC44S2InputPolynomial
  rw [SixC44S2Output_eval, SixC44S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC44S2InputSlices SixC44S2_cofactors
end SixCertificates
