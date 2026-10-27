import RawSixPart01
import MathAndTheory.Mathematics.Gyires.CirculantCertificate
import Mathlib.Tactic.FinCases
namespace RawSix
open MathAndTheory.Gyires.SparsePolynomial
open MathAndTheory.Gyires.CirculantCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def primes : Fin 6 → ℕ := ![2, 3, 5, 7, 11, 13]

theorem primes_prime : ∀ i, (primes i).Prime := by decide +kernel

theorem primes_injective : Function.Injective primes := by decide +kernel

theorem eval_p6 (f : ℕ →* ℝ) : eval f p6 = P6 ![f 2, f 3, f 5, f 7, f 11, f 13] := by
  simp only [p6, eval, map_mul, map_pow, P6, Matrix.cons_val]
  norm_num
  ring

theorem eval_gram (f : ℕ →* ℝ) :
    ![eval f b0, eval f b1, eval f b2, eval f b3, eval f b4, eval f b5] =
      gram6 ![f 2, f 3, f 5, f 7, f 11, f 13] := by
  ext i
  fin_cases i <;>
    simp only [b0, b1, b2, b3, b4, b5, eval, map_mul, map_pow, gram6, Matrix.cons_val] <;>
    norm_num <;> ring

theorem prime_values (w : Fin 6 → ℝ) :
    ![primeEvaluation primes w 2, primeEvaluation primes w 3,
      primeEvaluation primes w 5, primeEvaluation primes w 7,
      primeEvaluation primes w 11, primeEvaluation primes w 13] = w := by
  ext i
  fin_cases i
  · simpa [primes] using primeEvaluation_prime primes primes_prime primes_injective w 0
  · simpa [primes] using primeEvaluation_prime primes primes_prime primes_injective w 1
  · simpa [primes] using primeEvaluation_prime primes primes_prime primes_injective w 2
  · simpa [primes] using primeEvaluation_prime primes primes_prime primes_injective w 3
  · simpa [primes] using primeEvaluation_prime primes primes_prime primes_injective w 4
  · simpa [primes] using primeEvaluation_prime primes primes_prime primes_injective w 5

theorem matrix_gram (w : Fin 6 → ℝ) :
    circulant w * (circulant w).transpose = circulant (gram6 w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [circulant, gram6, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.sub_def, Fin.neg_def, Fin.add_def] <;> ring

#print axioms eval_p6
#print axioms eval_gram
#print axioms prime_values
#print axioms matrix_gram
end RawSix
