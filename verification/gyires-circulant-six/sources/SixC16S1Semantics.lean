import SixC16S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC16S1_cofactors : ∀ p ∈ SixC16S1InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC16S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC16S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 5))) SixC16S0OutputPolynomial := by
  change _ = eval _ SixC16S1InputPolynomial
  rw [SixC16S1Output_eval, SixC16S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 5 (by decide) SixC16S1InputSlices SixC16S1_cofactors
end SixCertificates
