import SixC26S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC26S2_cofactors : ∀ p ∈ SixC26S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC26S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC26S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC26S1OutputPolynomial := by
  change _ = eval _ SixC26S2InputPolynomial
  rw [SixC26S2Output_eval, SixC26S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC26S2InputSlices SixC26S2_cofactors
end SixCertificates
