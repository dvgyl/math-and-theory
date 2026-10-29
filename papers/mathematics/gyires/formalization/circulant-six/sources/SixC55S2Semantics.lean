import SixC55S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC55S2_cofactors : ∀ p ∈ SixC55S2InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC55S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC55S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 2))) SixC55S1OutputPolynomial := by
  change _ = eval _ SixC55S2InputPolynomial
  rw [SixC55S2Output_eval, SixC55S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 2 (by decide) SixC55S2InputSlices SixC55S2_cofactors
end SixCertificates
