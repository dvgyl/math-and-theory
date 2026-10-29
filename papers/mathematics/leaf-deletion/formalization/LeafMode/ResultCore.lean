import LeafMode.IsoInvariance
import LeafMode.Modes

/-! The explicit tree, actual leaf deletion, vertex counts, and exact polynomial formulas. -/
noncomputable section
open Polynomial

namespace LeafMode.Result

abbrev Tree := graph 662 9 1
def leaf : V 662 9 1 := V.extra 0
abbrev DeletedTree := Tree.induce {x | x ≠ leaf}

def corePolynomial : Polynomial ℤ :=
  X * Counting.S 9 ^ 662 + Counting.T 9 ^ 662 - (1 + X) ^ 5958

def treePolynomial : Polynomial ℤ :=
  (1 + X) * Counting.S 9 ^ 662 + Counting.T 9 ^ 662

theorem vertex_card (n k l : ℕ) : Fintype.card (V n k l) = 1 + n + n + n*k + l := by
  rw [Fintype.card_congr (Semantics.vertexEquiv n k l)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  omega

theorem tree_card : Fintype.card (V 662 9 1) = 7284 := by
  rw [vertex_card]

theorem deleted_card : Fintype.card {x : V 662 9 1 // x ≠ leaf} = 7283 := by
  change Fintype.card {x : V 662 9 1 // x ≠ V.extra 0} = 7283
  rw [← Fintype.card_congr (deleteLeafEquiv 662 9), vertex_card]

theorem is_tree : Tree.IsTree := graph_isTree 662 9 1

theorem leaf_degree : Tree.degree leaf = 1 := extra_degree 0

theorem core_formula :
    dominationPolynomial (graph 662 9 0) = (X : Polynomial ℤ) ^ 662 * corePolynomial := by
  rw [Semantics.dominationPolynomial_root (by decide), Counting.rootGF_eq (by decide)]
  rfl

theorem tree_formula :
    dominationPolynomial Tree = (X : Polynomial ℤ) ^ 663 * treePolynomial := by
  rw [Semantics.dominationPolynomial_extended (by decide), Counting.extendedGF_eq (by decide)]
  rfl

theorem deleted_formula :
    dominationPolynomial DeletedTree = (X : Polynomial ℤ) ^ 662 * corePolynomial := by
  have he := dominationPolynomial_iso (deleteLeafIso 662 9)
  change dominationPolynomial (graph 662 9 0) = dominationPolynomial DeletedTree at he
  rw [← he, core_formula]

end LeafMode.Result
