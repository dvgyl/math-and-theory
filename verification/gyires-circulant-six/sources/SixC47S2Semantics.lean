import SixC47S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC47S2_cofactors : ∀ p ∈ SixC47S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC47S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC47S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 5))) SixC47S1OutputPolynomial := by
  change _ = eval _ SixC47S2InputPolynomial
  rw [SixC47S2Output_eval, SixC47S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 5 (by decide) SixC47S2InputSlices SixC47S2_cofactors
end SixCertificates
