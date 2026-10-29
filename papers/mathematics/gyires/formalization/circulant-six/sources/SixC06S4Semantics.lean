import SixC06S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC06S4_cofactors : ∀ p ∈ SixC06S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC06S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC06S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC06S3OutputPolynomial := by
  change _ = eval _ SixC06S4InputPolynomial
  rw [SixC06S4Output_eval, SixC06S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC06S4InputSlices SixC06S4_cofactors
end SixCertificates
