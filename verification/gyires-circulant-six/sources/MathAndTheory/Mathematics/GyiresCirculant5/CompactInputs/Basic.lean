module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.ListPolynomial
public import MathAndTheory.Mathematics.GyiresCirculant5.FiniteVectorMap

/-!
# Equality of coefficient lists

Two lists of the same length are equal when all their coefficients agree. The generated files
use this to identify computed coefficient lists with their collected closed forms.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
namespace MathAndTheory.GyiresCirculant5

theorem polyList_eq_of_coeff (p q : List ℝ)
    (hlen : p.length = q.length)
    (hcoeff : ∀ k : Fin p.length, polyCoeff p k = polyCoeff q k) : p = q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q => simp at hlen
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      have hhead : a = b := hcoeff ⟨0, Nat.zero_lt_succ _⟩
      have htail : ∀ k : Fin p.length, polyCoeff p k = polyCoeff q k := by
        intro k
        exact hcoeff ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
      exact congrArg₂ List.cons hhead (ih q (Nat.succ.inj hlen) htail)

theorem polyList_eq_of_coeff_n (p q : List ℝ) (n : ℕ)
    (hp : p.length = n) (hq : q.length = n)
    (hcoeff : ∀ k : Fin n, polyCoeff p k = polyCoeff q k) : p = q := by
  apply polyList_eq_of_coeff p q (hp.trans hq.symm)
  intro k
  exact hcoeff ⟨k.val, by simpa only [hp] using k.isLt⟩

end MathAndTheory.GyiresCirculant5
