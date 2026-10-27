import SixC34S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC34S3_cofactors : ∀ p ∈ SixC34S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC34S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC34S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) SixC34S2OutputPolynomial := by
  change _ = eval _ SixC34S3InputPolynomial
  rw [SixC34S3Output_eval, SixC34S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC34S3InputSlices SixC34S3_cofactors
end SixCertificates
