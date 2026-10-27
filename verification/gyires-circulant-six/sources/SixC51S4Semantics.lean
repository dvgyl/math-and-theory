import SixC51S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC51S4_cofactors : ∀ p ∈ SixC51S4InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC51S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC51S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 0))) SixC51S3OutputPolynomial := by
  change _ = eval _ SixC51S4InputPolynomial
  rw [SixC51S4Output_eval, SixC51S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 0 (by decide) SixC51S4InputSlices SixC51S4_cofactors
end SixCertificates
