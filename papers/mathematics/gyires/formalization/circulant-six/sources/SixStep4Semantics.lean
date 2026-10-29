import SixStep4OutputMerge
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem step4_cofactors : ∀ p ∈ SixStep4InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem step4_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixStep4OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 0))) SixStep3OutputPolynomial := by
  change _ = eval _ SixStep4InputPolynomial
  rw [SixStep4Output_eval, SixStep4Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 0 (by decide) SixStep4InputSlices step4_cofactors
end ChamberSix0
