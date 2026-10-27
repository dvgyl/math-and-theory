import SixC07S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC07S2_cofactors : ∀ p ∈ SixC07S2InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC07S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC07S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) SixC07S1OutputPolynomial := by
  change _ = eval _ SixC07S2InputPolynomial
  rw [SixC07S2Output_eval, SixC07S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC07S2InputSlices SixC07S2_cofactors
end SixCertificates
