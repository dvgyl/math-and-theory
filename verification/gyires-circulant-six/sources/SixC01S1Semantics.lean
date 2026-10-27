import SixC01S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC01S1_cofactors : ∀ p ∈ SixC01S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC01S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC01S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) SixC01S0OutputPolynomial := by
  change _ = eval _ SixC01S1InputPolynomial
  rw [SixC01S1Output_eval, SixC01S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC01S1InputSlices SixC01S1_cofactors
end SixCertificates
