import SixC10S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC10S4_cofactors : ∀ p ∈ SixC10S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC10S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC10S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC10S3OutputPolynomial := by
  change _ = eval _ SixC10S4InputPolynomial
  rw [SixC10S4Output_eval, SixC10S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC10S4InputSlices SixC10S4_cofactors
end SixCertificates
