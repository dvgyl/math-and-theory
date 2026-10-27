import SixC24S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC24S4_cofactors : ∀ p ∈ SixC24S4InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC24S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC24S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 0))) SixC24S3OutputPolynomial := by
  change _ = eval _ SixC24S4InputPolynomial
  rw [SixC24S4Output_eval, SixC24S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 0 (by decide) SixC24S4InputSlices SixC24S4_cofactors
end SixCertificates
