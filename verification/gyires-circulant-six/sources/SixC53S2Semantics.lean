import SixC53S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC53S2_cofactors : ∀ p ∈ SixC53S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC53S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC53S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC53S1OutputPolynomial := by
  change _ = eval _ SixC53S2InputPolynomial
  rw [SixC53S2Output_eval, SixC53S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC53S2InputSlices SixC53S2_cofactors
end SixCertificates
