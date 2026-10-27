import SixCertificateBase
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
noncomputable def marginPolynomial : Polynomial :=
  [(3 ^ 12, 42624), (5 ^ 12, 42624), (7 ^ 12, 42624), (11 ^ 12, 42624), (13 ^ 12, 42624)]

def gapPowerSum (z : Fin 6 → ℝ) : ℝ := z 1 ^ 12 + z 2 ^ 12 + z 3 ^ 12 + z 4 ^ 12 + z 5 ^ 12

theorem eval_margin (z : Fin 6 → ℝ) :
    eval (primeEvaluation primes z) marginPolynomial = 42624 * gapPowerSum z := by
  have h1 := primeEvaluation_prime primes primes_prime primes_injective z 1
  have h2 := primeEvaluation_prime primes primes_prime primes_injective z 2
  have h3 := primeEvaluation_prime primes primes_prime primes_injective z 3
  have h4 := primeEvaluation_prime primes primes_prime primes_injective z 4
  have h5 := primeEvaluation_prime primes primes_prime primes_injective z 5
  simp only [primes, Matrix.cons_val] at h1 h2 h3 h4 h5
  simp only [marginPolynomial, eval, map_pow, primes, h1, h2, h3, h4, h5, gapPowerSum]
  norm_num
  ring
end SixCertificates
