import SixC02S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC02S1_cofactors : ∀ p ∈ SixC02S1InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC02S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC02S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 4))) SixC02S0OutputPolynomial := by
  change _ = eval _ SixC02S1InputPolynomial
  rw [SixC02S1Output_eval, SixC02S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 4 (by decide) SixC02S1InputSlices SixC02S1_cofactors
end SixCertificates
