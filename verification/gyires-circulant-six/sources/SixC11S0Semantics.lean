import SixC11S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC11S0_cofactors : ∀ p ∈ SixC11S0InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC11S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC11S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 4))) rawDense := by
  change _ = eval _ SixC11S0InputPolynomial
  rw [SixC11S0Output_eval, SixC11S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 4 (by decide) SixC11S0InputSlices SixC11S0_cofactors
end SixCertificates
