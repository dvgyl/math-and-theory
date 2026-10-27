import SixC50S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC50S4_cofactors : ∀ p ∈ SixC50S4InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC50S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC50S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 0))) SixC50S3OutputPolynomial := by
  change _ = eval _ SixC50S4InputPolynomial
  rw [SixC50S4Output_eval, SixC50S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 0 (by decide) SixC50S4InputSlices SixC50S4_cofactors
end SixCertificates
