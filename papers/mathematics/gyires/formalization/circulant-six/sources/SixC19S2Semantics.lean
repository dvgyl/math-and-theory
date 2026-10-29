import SixC19S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC19S2_cofactors : ∀ p ∈ SixC19S2InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC19S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC19S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 5))) SixC19S1OutputPolynomial := by
  change _ = eval _ SixC19S2InputPolynomial
  rw [SixC19S2Output_eval, SixC19S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 5 (by decide) SixC19S2InputSlices SixC19S2_cofactors
end SixCertificates
