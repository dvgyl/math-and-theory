import SixStep3OutputMerge
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem step3_cofactors : ∀ p ∈ SixStep3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem step3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixStep3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 1))) SixStep2OutputPolynomial := by
  change _ = eval _ SixStep3InputPolynomial
  rw [SixStep3Output_eval, SixStep3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 1 (by decide) SixStep3InputSlices step3_cofactors
end ChamberSix0
