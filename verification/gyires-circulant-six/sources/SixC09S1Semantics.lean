import SixC09S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC09S1_cofactors : ∀ p ∈ SixC09S1InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC09S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC09S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) SixC09S0OutputPolynomial := by
  change _ = eval _ SixC09S1InputPolynomial
  rw [SixC09S1Output_eval, SixC09S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC09S1InputSlices SixC09S1_cofactors
end SixCertificates
