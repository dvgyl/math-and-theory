import SixC37S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC37S2_cofactors : ∀ p ∈ SixC37S2InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC37S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC37S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 4))) SixC37S1OutputPolynomial := by
  change _ = eval _ SixC37S2InputPolynomial
  rw [SixC37S2Output_eval, SixC37S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 4 (by decide) SixC37S2InputSlices SixC37S2_cofactors
end SixCertificates
