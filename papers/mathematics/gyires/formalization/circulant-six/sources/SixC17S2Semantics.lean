import SixC17S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC17S2_cofactors : ∀ p ∈ SixC17S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC17S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC17S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) SixC17S1OutputPolynomial := by
  change _ = eval _ SixC17S2InputPolynomial
  rw [SixC17S2Output_eval, SixC17S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC17S2InputSlices SixC17S2_cofactors
end SixCertificates
