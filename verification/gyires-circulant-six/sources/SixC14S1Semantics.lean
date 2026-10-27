import SixC14S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC14S1_cofactors : ∀ p ∈ SixC14S1InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC14S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC14S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) SixC14S0OutputPolynomial := by
  change _ = eval _ SixC14S1InputPolynomial
  rw [SixC14S1Output_eval, SixC14S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC14S1InputSlices SixC14S1_cofactors
end SixCertificates
