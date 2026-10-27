import SixC37S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC37S0_cofactors : ∀ p ∈ SixC37S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC37S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC37S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 5))) rawDense := by
  change _ = eval _ SixC37S0InputPolynomial
  rw [SixC37S0Output_eval, SixC37S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 5 (by decide) SixC37S0InputSlices SixC37S0_cofactors
end SixCertificates
