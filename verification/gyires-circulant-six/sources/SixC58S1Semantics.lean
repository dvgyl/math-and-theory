import SixC58S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC58S1_cofactors : ∀ p ∈ SixC58S1InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC58S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC58S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 5))) SixC58S0OutputPolynomial := by
  change _ = eval _ SixC58S1InputPolynomial
  rw [SixC58S1Output_eval, SixC58S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 5 (by decide) SixC58S1InputSlices SixC58S1_cofactors
end SixCertificates
