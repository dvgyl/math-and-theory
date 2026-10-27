import SixC59S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC59S4_cofactors : ∀ p ∈ SixC59S4InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC59S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC59S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 0))) SixC59S3OutputPolynomial := by
  change _ = eval _ SixC59S4InputPolynomial
  rw [SixC59S4Output_eval, SixC59S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 0 (by decide) SixC59S4InputSlices SixC59S4_cofactors
end SixCertificates
