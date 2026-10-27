import SixC15S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC15S2_cofactors : ∀ p ∈ SixC15S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC15S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC15S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) SixC15S1OutputPolynomial := by
  change _ = eval _ SixC15S2InputPolynomial
  rw [SixC15S2Output_eval, SixC15S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC15S2InputSlices SixC15S2_cofactors
end SixCertificates
