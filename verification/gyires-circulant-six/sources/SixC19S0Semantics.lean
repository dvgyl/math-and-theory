import SixC19S0OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC19S0_cofactors : ∀ p ∈ SixC19S0InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC19S0_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC19S0OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) rawDense := by
  change _ = eval _ SixC19S0InputPolynomial
  rw [SixC19S0Output_eval, SixC19S0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC19S0InputSlices SixC19S0_cofactors
end SixCertificates
