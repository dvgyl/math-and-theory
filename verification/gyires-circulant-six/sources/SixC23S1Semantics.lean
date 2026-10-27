import SixC23S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC23S1_cofactors : ∀ p ∈ SixC23S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC23S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC23S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) SixC23S0OutputPolynomial := by
  change _ = eval _ SixC23S1InputPolynomial
  rw [SixC23S1Output_eval, SixC23S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC23S1InputSlices SixC23S1_cofactors
end SixCertificates
