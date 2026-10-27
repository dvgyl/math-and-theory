import SixC49S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC49S4_cofactors : ∀ p ∈ SixC49S4InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC49S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC49S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 0))) SixC49S3OutputPolynomial := by
  change _ = eval _ SixC49S4InputPolynomial
  rw [SixC49S4Output_eval, SixC49S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 0 (by decide) SixC49S4InputSlices SixC49S4_cofactors
end SixCertificates
