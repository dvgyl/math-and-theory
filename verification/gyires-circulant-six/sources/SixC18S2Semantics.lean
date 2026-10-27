import SixC18S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC18S2_cofactors : ∀ p ∈ SixC18S2InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC18S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC18S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 5))) SixC18S1OutputPolynomial := by
  change _ = eval _ SixC18S2InputPolynomial
  rw [SixC18S2Output_eval, SixC18S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 5 (by decide) SixC18S2InputSlices SixC18S2_cofactors
end SixCertificates
