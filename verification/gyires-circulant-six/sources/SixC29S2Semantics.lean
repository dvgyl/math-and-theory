import SixC29S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC29S2_cofactors : ∀ p ∈ SixC29S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC29S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC29S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC29S1OutputPolynomial := by
  change _ = eval _ SixC29S2InputPolynomial
  rw [SixC29S2Output_eval, SixC29S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC29S2InputSlices SixC29S2_cofactors
end SixCertificates
