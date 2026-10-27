import SixC16S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC16S0_cofactors : ∀ p ∈ SixC16S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC16S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC16S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) rawDense := by
  change _ = eval _ SixC16S0InputPolynomial
  rw [SixC16S0Output_eval, SixC16S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC16S0InputSlices SixC16S0_cofactors
end SixCertificates
