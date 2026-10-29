import BookOuterSimplicity
import Mathlib.Data.Multiset.Filter

noncomputable section
namespace BookCompletion

theorem real_roots_eq_four_of_classification (n : ℕ) (hn : 1 ≤ n) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hclass : ∀ x : ℝ, (realPolynomial n).IsRoot x ↔ x = 0 ∨ x = a ∨ x = b)
    (hma : (realPolynomial n).rootMultiplicity a = 1)
    (hmb : (realPolynomial n).rootMultiplicity b = 1) :
    (realPolynomial n).roots = 0 ::ₘ 0 ::ₘ a ::ₘ b ::ₘ (0 : Multiset ℝ) := by
  classical
  ext x
  rw [Polynomial.count_roots]
  by_cases hx0 : x = 0
  · subst x
    rw [realPolynomial_origin_multiplicity n hn]
    simp [ha,hb,Ne.symm ha,Ne.symm hb]
  by_cases hxa : x = a
  · subst x
    rw [hma]
    simp [ha,hab,Ne.symm hab]
  by_cases hxb : x = b
  · subst x
    rw [hmb]
    simp [hb,hab,Ne.symm hab]
  have hnot : ¬(realPolynomial n).IsRoot x := by
    rw [hclass x]
    simp [hx0,hxa,hxb]
  rw [Polynomial.rootMultiplicity_eq_zero hnot]
  simp [hx0,hxa,hxb,Ne.symm hx0,Ne.symm hxa,Ne.symm hxb]

theorem real_roots_card_four_of_classification (n : ℕ) (hn : 1 ≤ n) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hclass : ∀ x : ℝ, (realPolynomial n).IsRoot x ↔ x = 0 ∨ x = a ∨ x = b)
    (hma : (realPolynomial n).rootMultiplicity a = 1)
    (hmb : (realPolynomial n).rootMultiplicity b = 1) :
    (realPolynomial n).roots.card = 4 := by
  rw [real_roots_eq_four_of_classification n hn ha hb hab hclass hma hmb]
  simp

#print axioms real_roots_eq_four_of_classification
#print axioms real_roots_card_four_of_classification
end BookCompletion
