import SixStep0OutputMerge
import Mathlib.Data.Fin.VecNotation
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def primes : Fin 6 → ℕ := ![2, 3, 5, 7, 11, 13]

theorem primes_prime : ∀ i, (primes i).Prime := by decide +kernel

theorem primes_injective : Function.Injective primes := by decide +kernel

theorem step0_cofactors : ∀ p ∈ SixStep0InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel

theorem step0_eval (z : Fin 6 → ℝ) :
    eval (primeEvaluation primes z) SixStep0OutputPolynomial =
      eval (primeEvaluation primes (Function.update z 5 (z 5 + z 4))) SixStep0InputPolynomial := by
  rw [SixStep0Output_eval, SixStep0Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 4 (by decide)
    SixStep0InputSlices step0_cofactors

#print axioms step0_eval
end ChamberSix0
