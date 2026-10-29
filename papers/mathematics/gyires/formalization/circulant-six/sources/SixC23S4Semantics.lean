import SixC23S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC23S4_cofactors : ∀ p ∈ SixC23S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC23S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC23S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC23S3OutputPolynomial := by
  change _ = eval _ SixC23S4InputPolynomial
  rw [SixC23S4Output_eval, SixC23S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC23S4InputSlices SixC23S4_cofactors
end SixCertificates
