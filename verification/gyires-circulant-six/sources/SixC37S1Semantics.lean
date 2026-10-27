import SixC37S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC37S1_cofactors : ∀ p ∈ SixC37S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC37S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC37S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC37S0OutputPolynomial := by
  change _ = eval _ SixC37S1InputPolynomial
  rw [SixC37S1Output_eval, SixC37S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC37S1InputSlices SixC37S1_cofactors
end SixCertificates
