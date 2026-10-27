import SixC11S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC11S1_cofactors : ∀ p ∈ SixC11S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC11S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC11S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) SixC11S0OutputPolynomial := by
  change _ = eval _ SixC11S1InputPolynomial
  rw [SixC11S1Output_eval, SixC11S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC11S1InputSlices SixC11S1_cofactors
end SixCertificates
