import SixC29S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC29S1_cofactors : ∀ p ∈ SixC29S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC29S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC29S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) SixC29S0OutputPolynomial := by
  change _ = eval _ SixC29S1InputPolynomial
  rw [SixC29S1Output_eval, SixC29S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC29S1InputSlices SixC29S1_cofactors
end SixCertificates
