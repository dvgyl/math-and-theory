import SixC20S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC20S2_cofactors : ∀ p ∈ SixC20S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC20S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC20S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) SixC20S1OutputPolynomial := by
  change _ = eval _ SixC20S2InputPolynomial
  rw [SixC20S2Output_eval, SixC20S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC20S2InputSlices SixC20S2_cofactors
end SixCertificates
