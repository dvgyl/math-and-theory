import SixC08S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC08S2_cofactors : ∀ p ∈ SixC08S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC08S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC08S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) SixC08S1OutputPolynomial := by
  change _ = eval _ SixC08S2InputPolynomial
  rw [SixC08S2Output_eval, SixC08S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC08S2InputSlices SixC08S2_cofactors
end SixCertificates
