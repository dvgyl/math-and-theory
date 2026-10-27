import SixC26S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC26S0_cofactors : ∀ p ∈ SixC26S0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC26S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC26S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 3))) rawDense := by
  change _ = eval _ SixC26S0InputPolynomial
  rw [SixC26S0Output_eval, SixC26S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 3 (by decide) SixC26S0InputSlices SixC26S0_cofactors
end SixCertificates
