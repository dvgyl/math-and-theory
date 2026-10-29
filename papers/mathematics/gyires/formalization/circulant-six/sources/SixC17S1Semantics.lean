import SixC17S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC17S1_cofactors : ∀ p ∈ SixC17S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC17S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC17S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) SixC17S0OutputPolynomial := by
  change _ = eval _ SixC17S1InputPolynomial
  rw [SixC17S1Output_eval, SixC17S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC17S1InputSlices SixC17S1_cofactors
end SixCertificates
