import SixC33S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC33S2_cofactors : ∀ p ∈ SixC33S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC33S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC33S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) SixC33S1OutputPolynomial := by
  change _ = eval _ SixC33S2InputPolynomial
  rw [SixC33S2Output_eval, SixC33S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC33S2InputSlices SixC33S2_cofactors
end SixCertificates
