import SixC42S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC42S2_cofactors : ∀ p ∈ SixC42S2InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC42S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC42S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 5))) SixC42S1OutputPolynomial := by
  change _ = eval _ SixC42S2InputPolynomial
  rw [SixC42S2Output_eval, SixC42S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 5 (by decide) SixC42S2InputSlices SixC42S2_cofactors
end SixCertificates
