import LeafMode.ResultCore
import LeafMode.Certificates

/-! A complete explicit counterexample to the leaf-deletion mode-distance conjecture. -/
noncomputable section
open Polynomial

namespace LeafMode.Result
open Modes

attribute [local instance] Classical.propDecidable

theorem tree_unimodal : UnimodalAt (dominationPolynomial Tree) 3978 := by
  rw [tree_formula]
  change UnimodalAt ((X : Polynomial ℤ) ^ 663 * Cert.Q) (663 + 3315)
  exact shift_unimodal Cert.q_nonneg ⟨Cert.q_up, Cert.q_down⟩ 663

theorem deleted_unimodal : UnimodalAt (dominationPolynomial DeletedTree) 3976 := by
  rw [deleted_formula]
  change UnimodalAt ((X : Polynomial ℤ) ^ 662 * Cert.P) (662 + 3314)
  exact shift_unimodal Cert.p_nonneg ⟨Cert.p_up, Cert.p_down⟩ 662

theorem tree_unique_mode : UniqueMode (dominationPolynomial Tree) 3978 := by
  rw [tree_formula]
  change UniqueMode ((X : Polynomial ℤ) ^ 663 * Cert.Q) (663 + 3315)
  exact shift_unique Cert.q_positive Cert.q_unique 663

theorem deleted_unique_mode : UniqueMode (dominationPolynomial DeletedTree) 3976 := by
  rw [deleted_formula]
  change UniqueMode ((X : Polynomial ℤ) ^ 662 * Cert.P) (662 + 3314)
  exact shift_unique Cert.p_positive Cert.p_unique 662

theorem tree_mode_iff (i : ℕ) : IsMode (dominationPolynomial Tree) i ↔ i = 3978 :=
  unique_mode_iff tree_unique_mode i

theorem deleted_mode_iff (i : ℕ) :
    IsMode (dominationPolynomial DeletedTree) i ↔ i = 3976 :=
  unique_mode_iff deleted_unique_mode i

theorem no_close_modes :
    ¬ ModesClose (dominationPolynomial Tree) (dominationPolynomial DeletedTree) := by
  intro h
  exact not_modesClose deleted_unique_mode tree_unique_mode (by decide)
    (modesClose_comm.mp h)

/-- All hypotheses of the published question hold for this actual tree and actual leaf deletion. -/
theorem counterexample :
    Tree.IsTree ∧ Tree.degree leaf = 1 ∧
    UnimodalAt (dominationPolynomial Tree) 3978 ∧
    UnimodalAt (dominationPolynomial DeletedTree) 3976 ∧
    UniqueMode (dominationPolynomial Tree) 3978 ∧
    UniqueMode (dominationPolynomial DeletedTree) 3976 ∧
    ¬ ModesClose (dominationPolynomial Tree) (dominationPolynomial DeletedTree) :=
  ⟨is_tree, leaf_degree, tree_unimodal, deleted_unimodal,
    tree_unique_mode, deleted_unique_mode, no_close_modes⟩

/-- An affirmative answer to Question 8.1 of Amanda Burcroff and Grace O'Brien:
both domination polynomials are unimodal, yet no pair of modes has distance at most one. -/
theorem question_8_1 :
    ∃ (T : SimpleGraph (V 662 9 1)) (v : V 662 9 1),
      T.IsTree ∧ T.degree v = 1 ∧
      (∃ m, UnimodalAt (dominationPolynomial T) m) ∧
      (∃ m, UnimodalAt (dominationPolynomial (T.induce {x | x ≠ v})) m) ∧
      ¬ ModesClose (dominationPolynomial T)
        (dominationPolynomial (T.induce {x | x ≠ v})) := by
  refine ⟨Tree, leaf, is_tree, ?_, ⟨3978, tree_unimodal⟩,
    ⟨3976, deleted_unimodal⟩, no_close_modes⟩
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
    using leaf_degree

end LeafMode.Result
