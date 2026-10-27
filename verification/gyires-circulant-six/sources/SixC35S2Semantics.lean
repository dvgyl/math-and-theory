import SixC35S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC35S2_cofactors : ∀ p ∈ SixC35S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC35S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC35S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) SixC35S1OutputPolynomial := by
  change _ = eval _ SixC35S2InputPolynomial
  rw [SixC35S2Output_eval, SixC35S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC35S2InputSlices SixC35S2_cofactors
end SixCertificates
