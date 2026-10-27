import SixC01S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC01S4_cofactors : ∀ p ∈ SixC01S4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC01S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC01S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixC01S3OutputPolynomial := by
  change _ = eval _ SixC01S4InputPolynomial
  rw [SixC01S4Output_eval, SixC01S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixC01S4InputSlices SixC01S4_cofactors
end SixCertificates
