import SixC58S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC58S0_cofactors : ∀ p ∈ SixC58S0InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC58S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC58S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) rawDense := by
  change _ = eval _ SixC58S0InputPolynomial
  rw [SixC58S0Output_eval, SixC58S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC58S0InputSlices SixC58S0_cofactors
end SixCertificates
