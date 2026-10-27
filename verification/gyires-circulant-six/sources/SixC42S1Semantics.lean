import SixC42S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC42S1_cofactors : ∀ p ∈ SixC42S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC42S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC42S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) SixC42S0OutputPolynomial := by
  change _ = eval _ SixC42S1InputPolynomial
  rw [SixC42S1Output_eval, SixC42S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC42S1InputSlices SixC42S1_cofactors
end SixCertificates
