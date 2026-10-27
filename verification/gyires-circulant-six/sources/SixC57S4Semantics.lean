import SixC57S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC57S4_cofactors : ∀ p ∈ SixC57S4InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC57S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC57S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 0))) SixC57S3OutputPolynomial := by
  change _ = eval _ SixC57S4InputPolynomial
  rw [SixC57S4Output_eval, SixC57S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 0 (by decide) SixC57S4InputSlices SixC57S4_cofactors
end SixCertificates
