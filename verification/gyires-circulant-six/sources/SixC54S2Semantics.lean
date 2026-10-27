import SixC54S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC54S2_cofactors : ∀ p ∈ SixC54S2InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC54S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC54S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 2))) SixC54S1OutputPolynomial := by
  change _ = eval _ SixC54S2InputPolynomial
  rw [SixC54S2Output_eval, SixC54S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 2 (by decide) SixC54S2InputSlices SixC54S2_cofactors
end SixCertificates
