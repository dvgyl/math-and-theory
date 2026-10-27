import SixC50S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC50S2_cofactors : ∀ p ∈ SixC50S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC50S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC50S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC50S1OutputPolynomial := by
  change _ = eval _ SixC50S2InputPolynomial
  rw [SixC50S2Output_eval, SixC50S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC50S2InputSlices SixC50S2_cofactors
end SixCertificates
