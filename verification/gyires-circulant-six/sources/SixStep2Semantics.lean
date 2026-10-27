import SixStep2OutputMerge
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem step2_cofactors : ∀ p ∈ SixStep2InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem step2_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixStep2OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) SixStep1OutputPolynomial := by
  change _ = eval _ SixStep2InputPolynomial
  rw [SixStep2Output_eval, SixStep2Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixStep2InputSlices step2_cofactors
end ChamberSix0
