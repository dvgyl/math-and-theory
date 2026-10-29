import SixC01S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC01S2_cofactors : ∀ p ∈ SixC01S2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC01S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC01S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) SixC01S1OutputPolynomial := by
  change _ = eval _ SixC01S2InputPolynomial
  rw [SixC01S2Output_eval, SixC01S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC01S2InputSlices SixC01S2_cofactors
end SixCertificates
