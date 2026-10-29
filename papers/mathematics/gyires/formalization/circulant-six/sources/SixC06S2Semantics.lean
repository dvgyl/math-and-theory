import SixC06S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC06S2_cofactors : ∀ p ∈ SixC06S2InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC06S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC06S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) SixC06S1OutputPolynomial := by
  change _ = eval _ SixC06S2InputPolynomial
  rw [SixC06S2Output_eval, SixC06S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC06S2InputSlices SixC06S2_cofactors
end SixCertificates
