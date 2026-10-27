import SixC23S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC23S2_cofactors : ∀ p ∈ SixC23S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC23S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC23S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) SixC23S1OutputPolynomial := by
  change _ = eval _ SixC23S2InputPolynomial
  rw [SixC23S2Output_eval, SixC23S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC23S2InputSlices SixC23S2_cofactors
end SixCertificates
