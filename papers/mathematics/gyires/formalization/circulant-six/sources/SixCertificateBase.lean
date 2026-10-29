import SparsePolynomial
import SixRepresentatives
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial

def primes : Fin 6 → ℕ := ![2, 3, 5, 7, 11, 13]
theorem primes_prime : ∀ i, (primes i).Prime := by decide +kernel
theorem primes_injective : Function.Injective primes := by decide +kernel

def prefixVector (σ : Fin 6 → Fin 6) (z : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let a := Function.update z (σ 1) (z (σ 1) + z (σ 0))
  let b := Function.update a (σ 2) (a (σ 2) + a (σ 1))
  let c := Function.update b (σ 3) (b (σ 3) + b (σ 2))
  let d := Function.update c (σ 4) (c (σ 4) + c (σ 3))
  Function.update d (σ 5) (d (σ 5) + d (σ 4))
end SixCertificates
