import SixC33S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC33S4_cofactors : ∀ p ∈ SixC33S4InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC33S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC33S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 0))) SixC33S3OutputPolynomial := by
  change _ = eval _ SixC33S4InputPolynomial
  rw [SixC33S4Output_eval, SixC33S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 0 (by decide) SixC33S4InputSlices SixC33S4_cofactors
end SixCertificates
