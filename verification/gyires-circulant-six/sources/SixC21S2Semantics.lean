import SixC21S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC21S2_cofactors : ∀ p ∈ SixC21S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC21S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC21S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) SixC21S1OutputPolynomial := by
  change _ = eval _ SixC21S2InputPolynomial
  rw [SixC21S2Output_eval, SixC21S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC21S2InputSlices SixC21S2_cofactors
end SixCertificates
