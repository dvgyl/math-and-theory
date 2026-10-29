import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
namespace PowerRank

/-- Y and Z exponent vector; the X variable remains in the coefficient ring. -/
def biIndex (j c : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 j + Finsupp.single 1 c

section Generic
variable {R : Type*} [CommSemiring R]

def trinomialGenerator (A B D : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.monomial 0 A + MvPolynomial.monomial (biIndex 1 0) B +
    MvPolynomial.monomial (biIndex 2 1) D

/-- A full all-power expansion, with two independent binomial choices. -/
theorem trinomialGenerator_pow (A B D : R) (M : ℕ) :
    trinomialGenerator A B D ^ M =
      ∑ c ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M - c + 1),
        MvPolynomial.monomial (biIndex (b + 2 * c) c)
          (A ^ (M - c - b) * B ^ b * D ^ c * (M.choose c : R) * ((M - c).choose b : R)) := by
  classical
  have hcast (n : ℕ) : (n : MvPolynomial (Fin 2) R) = MvPolynomial.monomial 0 (n : R) := by
    rw [← MvPolynomial.C_apply]
    exact (map_natCast MvPolynomial.C n).symm
  rw [show trinomialGenerator A B D =
      MvPolynomial.monomial (biIndex 2 1) D +
        (MvPolynomial.monomial (biIndex 1 0) B + MvPolynomial.monomial 0 A) by
      unfold trinomialGenerator
      ac_rfl, add_pow]
  apply Finset.sum_congr rfl
  intro c hc
  rw [add_pow, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hcast, hcast, MvPolynomial.monomial_pow, MvPolynomial.monomial_pow,
    MvPolynomial.monomial_pow]
  simp only [MvPolynomial.monomial_mul_monomial]
  have hindex : c • biIndex 2 1 + (b • biIndex 1 0 + (M - c - b) • (0 : Fin 2 →₀ ℕ) + 0) + 0 =
      biIndex (b + 2 * c) c := by
    ext i
    fin_cases i <;> simp [biIndex]
    omega
  rw [hindex]
  congr 1
  ring

end Generic
end PowerRank
