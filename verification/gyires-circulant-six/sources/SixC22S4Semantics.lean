import SixC22S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC22S4_cofactors : ∀ p ∈ SixC22S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC22S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC22S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC22S3OutputPolynomial := by
  change _ = eval _ SixC22S4InputPolynomial
  rw [SixC22S4Output_eval, SixC22S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC22S4InputSlices SixC22S4_cofactors
end SixCertificates
