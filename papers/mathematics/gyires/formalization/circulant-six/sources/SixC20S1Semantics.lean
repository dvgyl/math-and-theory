import SixC20S1OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC20S1_cofactors : ∀ p ∈ SixC20S1InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC20S1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC20S1OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) SixC20S0OutputPolynomial := by
  change _ = eval _ SixC20S1InputPolynomial
  rw [SixC20S1Output_eval, SixC20S1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC20S1InputSlices SixC20S1_cofactors
end SixCertificates
