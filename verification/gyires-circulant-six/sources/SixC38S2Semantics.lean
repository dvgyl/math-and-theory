import SixC38S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC38S2_cofactors : ∀ p ∈ SixC38S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC38S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC38S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) SixC38S1OutputPolynomial := by
  change _ = eval _ SixC38S2InputPolynomial
  rw [SixC38S2Output_eval, SixC38S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC38S2InputSlices SixC38S2_cofactors
end SixCertificates
