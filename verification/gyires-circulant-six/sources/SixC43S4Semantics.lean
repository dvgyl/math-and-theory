import SixC43S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC43S4_cofactors : ∀ p ∈ SixC43S4InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC43S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC43S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 0))) SixC43S3OutputPolynomial := by
  change _ = eval _ SixC43S4InputPolynomial
  rw [SixC43S4Output_eval, SixC43S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 0 (by decide) SixC43S4InputSlices SixC43S4_cofactors
end SixCertificates
