import SixC22S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC22S1_cofactors : ∀ p ∈ SixC22S1InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC22S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC22S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 4))) SixC22S0OutputPolynomial := by
  change _ = eval _ SixC22S1InputPolynomial
  rw [SixC22S1Output_eval, SixC22S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 4 (by decide) SixC22S1InputSlices SixC22S1_cofactors
end SixCertificates
