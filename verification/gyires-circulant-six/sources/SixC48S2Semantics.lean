import SixC48S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC48S2_cofactors : ∀ p ∈ SixC48S2InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC48S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC48S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 1))) SixC48S1OutputPolynomial := by
  change _ = eval _ SixC48S2InputPolynomial
  rw [SixC48S2Output_eval, SixC48S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 1 (by decide) SixC48S2InputSlices SixC48S2_cofactors
end SixCertificates
