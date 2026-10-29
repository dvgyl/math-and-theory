import SixC58S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC58S4_cofactors : ∀ p ∈ SixC58S4InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC58S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC58S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 0))) SixC58S3OutputPolynomial := by
  change _ = eval _ SixC58S4InputPolynomial
  rw [SixC58S4Output_eval, SixC58S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 0 (by decide) SixC58S4InputSlices SixC58S4_cofactors
end SixCertificates
