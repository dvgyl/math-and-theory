import SixC48S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC48S4_cofactors : ∀ p ∈ SixC48S4InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC48S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC48S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 0))) SixC48S3OutputPolynomial := by
  change _ = eval _ SixC48S4InputPolynomial
  rw [SixC48S4Output_eval, SixC48S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 0 (by decide) SixC48S4InputSlices SixC48S4_cofactors
end SixCertificates
