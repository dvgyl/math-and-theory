import SixC08S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC08S4_cofactors : ∀ p ∈ SixC08S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC08S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC08S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC08S3OutputPolynomial := by
  change _ = eval _ SixC08S4InputPolynomial
  rw [SixC08S4Output_eval, SixC08S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC08S4InputSlices SixC08S4_cofactors
end SixCertificates
