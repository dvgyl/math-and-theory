import SixC20S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC20S4_cofactors : ∀ p ∈ SixC20S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC20S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC20S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC20S3OutputPolynomial := by
  change _ = eval _ SixC20S4InputPolynomial
  rw [SixC20S4Output_eval, SixC20S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC20S4InputSlices SixC20S4_cofactors
end SixCertificates
