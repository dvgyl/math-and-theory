import SixC16S2OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC16S2_cofactors : ∀ p ∈ SixC16S2InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC16S2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC16S2OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) SixC16S1OutputPolynomial := by
  change _ = eval _ SixC16S2InputPolynomial
  rw [SixC16S2Output_eval, SixC16S2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide) SixC16S2InputSlices SixC16S2_cofactors
end SixCertificates
