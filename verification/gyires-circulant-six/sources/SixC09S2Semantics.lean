import SixC09S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC09S2_cofactors : ∀ p ∈ SixC09S2InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC09S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC09S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) SixC09S1OutputPolynomial := by
  change _ = eval _ SixC09S2InputPolynomial
  rw [SixC09S2Output_eval, SixC09S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixC09S2InputSlices SixC09S2_cofactors
end SixCertificates
