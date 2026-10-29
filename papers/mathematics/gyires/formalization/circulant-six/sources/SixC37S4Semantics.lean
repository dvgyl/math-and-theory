import SixC37S4OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC37S4_cofactors : ∀ p ∈ SixC37S4InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC37S4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC37S4OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 0))) SixC37S3OutputPolynomial := by
  change _ = eval _ SixC37S4InputPolynomial
  rw [SixC37S4Output_eval, SixC37S4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 0 (by decide) SixC37S4InputSlices SixC37S4_cofactors
end SixCertificates
