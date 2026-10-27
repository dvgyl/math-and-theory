import SixC46S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC46S2_cofactors : ∀ p ∈ SixC46S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC46S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC46S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) SixC46S1OutputPolynomial := by
  change _ = eval _ SixC46S2InputPolynomial
  rw [SixC46S2Output_eval, SixC46S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC46S2InputSlices SixC46S2_cofactors
end SixCertificates
