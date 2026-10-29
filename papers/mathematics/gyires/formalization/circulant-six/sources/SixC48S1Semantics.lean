import SixC48S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC48S1_cofactors : ∀ p ∈ SixC48S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC48S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC48S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC48S0OutputPolynomial := by
  change _ = eval _ SixC48S1InputPolynomial
  rw [SixC48S1Output_eval, SixC48S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC48S1InputSlices SixC48S1_cofactors
end SixCertificates
