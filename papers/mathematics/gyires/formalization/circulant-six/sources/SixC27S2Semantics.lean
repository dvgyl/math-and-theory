import SixC27S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC27S2_cofactors : ∀ p ∈ SixC27S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC27S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC27S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC27S1OutputPolynomial := by
  change _ = eval _ SixC27S2InputPolynomial
  rw [SixC27S2Output_eval, SixC27S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC27S2InputSlices SixC27S2_cofactors
end SixCertificates
