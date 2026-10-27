import SixC34S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC34S0_cofactors : ∀ p ∈ SixC34S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC34S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC34S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) rawDense := by
  change _ = eval _ SixC34S0InputPolynomial
  rw [SixC34S0Output_eval, SixC34S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC34S0InputSlices SixC34S0_cofactors
end SixCertificates
