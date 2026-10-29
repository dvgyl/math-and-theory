import SixStep1OutputMerge
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem step1_cofactors : ∀ p ∈ SixStep1InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem step1_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixStep1OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 3))) SixStep0OutputPolynomial := by
  change _ = eval _ SixStep1InputPolynomial
  rw [SixStep1Output_eval, SixStep1Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 3 (by decide) SixStep1InputSlices step1_cofactors
end ChamberSix0
