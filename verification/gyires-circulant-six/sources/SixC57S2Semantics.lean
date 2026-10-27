import SixC57S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC57S2_cofactors : ∀ p ∈ SixC57S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC57S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC57S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC57S1OutputPolynomial := by
  change _ = eval _ SixC57S2InputPolynomial
  rw [SixC57S2Output_eval, SixC57S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC57S2InputSlices SixC57S2_cofactors
end SixCertificates
