import SixC21S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC21S1_cofactors : ∀ p ∈ SixC21S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC21S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC21S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) SixC21S0OutputPolynomial := by
  change _ = eval _ SixC21S1InputPolynomial
  rw [SixC21S1Output_eval, SixC21S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC21S1InputSlices SixC21S1_cofactors
end SixCertificates
