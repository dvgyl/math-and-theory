import SixC31S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC31S2_cofactors : ∀ p ∈ SixC31S2InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC31S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC31S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) SixC31S1OutputPolynomial := by
  change _ = eval _ SixC31S2InputPolynomial
  rw [SixC31S2Output_eval, SixC31S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC31S2InputSlices SixC31S2_cofactors
end SixCertificates
