import SixC13S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC13S2_cofactors : ∀ p ∈ SixC13S2InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC13S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC13S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 4))) SixC13S1OutputPolynomial := by
  change _ = eval _ SixC13S2InputPolynomial
  rw [SixC13S2Output_eval, SixC13S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 4 (by decide) SixC13S2InputSlices SixC13S2_cofactors
end SixCertificates
