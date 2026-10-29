import BookOrigin
import Mathlib.Data.Complex.Basic

noncomputable section
open scoped BigOperators
open Polynomial
open SquareFlowerCompletion.Counting
namespace BookCompletion
attribute [local instance] Classical.propDecidable

def complexPolynomial (n : ℕ) : Polynomial ℂ :=
  (dominationPolynomial (book n)).map (Int.castRingHom ℂ)

theorem map_realPolynomial (n : ℕ) :
    (realPolynomial n).map Complex.ofRealHom = complexPolynomial n := by
  rw [realPolynomial, Polynomial.map_map, complexPolynomial]
  congr 1

theorem complexPolynomial_origin_multiplicity (n : ℕ) (hn : 1 ≤ n) :
    (complexPolynomial n).rootMultiplicity 0 = 2 := by
  have h := Polynomial.eq_rootMultiplicity_map (p:=realPolynomial n)
    (f:=Complex.ofRealHom) Complex.ofReal_injective (0:ℝ)
  rw [map_zero, map_realPolynomial, realPolynomial_origin_multiplicity n hn] at h
  exact h.symm

theorem eval_realPolynomial_subsets (n : ℕ) (x : ℝ) :
    (realPolynomial n).eval x = ∑ s : Finset (Vertex n),
      if Dominates (book n) s then x^s.card else 0 := by
  rw [realPolynomial, dominationPolynomial, Polynomial.map_sum, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : Dominates (book n) s <;> simp [h]

theorem eval_realPolynomial_positive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (realPolynomial n).eval x := by
  rw [eval_realPolynomial_subsets]
  apply Finset.sum_pos'
  · intro s hs
    split_ifs <;> positivity
  · refine ⟨Finset.univ, Finset.mem_univ _, ?_⟩
    have hdom : Dominates (book n) Finset.univ := by
      intro v
      exact Or.inl (Finset.mem_univ _)
    simp only [hdom, ite_true]
    exact pow_pos hx _

theorem realPolynomial_nonpositive_root (n : ℕ) {x : ℝ}
    (hroot : (realPolynomial n).IsRoot x) : x ≤ 0 := by
  by_contra h
  have hx : 0 < x := lt_of_not_ge h
  have hp := eval_realPolynomial_positive n hx
  rw [Polynomial.IsRoot.def] at hroot
  linarith

theorem complexPolynomial_one_real_roots (x : ℝ) :
    (complexPolynomial 1).IsRoot (x:ℂ) ↔ x=0 := by
  rw [← map_realPolynomial, Polynomial.IsRoot.def, eval_map]
  change ((realPolynomial 1).eval₂ Complex.ofRealHom (Complex.ofRealHom x) = 0) ↔ x=0
  rw [eval₂_at_apply]
  change (Complex.ofReal ((realPolynomial 1).eval x)=0) ↔ x=0
  rw [Complex.ofReal_eq_zero]
  exact realPolynomial_one_roots x

#print axioms map_realPolynomial
#print axioms complexPolynomial_origin_multiplicity
#print axioms eval_realPolynomial_subsets
#print axioms eval_realPolynomial_positive
#print axioms realPolynomial_nonpositive_root
#print axioms complexPolynomial_one_real_roots
end BookCompletion
