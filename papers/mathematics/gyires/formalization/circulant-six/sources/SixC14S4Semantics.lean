import SixC14S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC14S4_cofactors : ∀ p ∈ SixC14S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC14S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC14S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC14S3OutputPolynomial := by
  change _ = eval _ SixC14S4InputPolynomial
  rw [SixC14S4Output_eval, SixC14S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC14S4InputSlices SixC14S4_cofactors
end SixCertificates
