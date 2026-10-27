import SixC13S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC13S1_cofactors : ∀ p ∈ SixC13S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC13S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC13S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC13S0OutputPolynomial := by
  change _ = eval _ SixC13S1InputPolynomial
  rw [SixC13S1Output_eval, SixC13S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC13S1InputSlices SixC13S1_cofactors
end SixCertificates
