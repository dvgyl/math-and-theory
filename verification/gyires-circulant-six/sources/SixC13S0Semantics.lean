import SixC13S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC13S0_cofactors : ∀ p ∈ SixC13S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC13S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC13S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) rawDense := by
  change _ = eval _ SixC13S0InputPolynomial
  rw [SixC13S0Output_eval, SixC13S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC13S0InputSlices SixC13S0_cofactors
end SixCertificates
