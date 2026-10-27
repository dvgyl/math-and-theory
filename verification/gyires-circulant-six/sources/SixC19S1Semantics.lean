import SixC19S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC19S1_cofactors : ∀ p ∈ SixC19S1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC19S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC19S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC19S0OutputPolynomial := by
  change _ = eval _ SixC19S1InputPolynomial
  rw [SixC19S1Output_eval, SixC19S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC19S1InputSlices SixC19S1_cofactors
end SixCertificates
