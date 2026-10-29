module
public import HS.CertificateParts.Sparse

@[expose] public section

/-! A direct expression tree avoids repeated list slicing during definitional
conversion. Its flattening is a difference-list traversal, and all generated
coefficient merges are checked by ordinary kernel reduction. -/

namespace HS.CertificateParts

set_option autoImplicit false

inductive CoefficientTree where
  | empty
  | leaf (key : ℕ) (coefficient : ℤ)
  | node (left right : CoefficientTree)

def treeEval {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) : CoefficientTree → R
  | .empty => 0
  | .leaf k c => term k c
  | .node p q => treeEval term p + treeEval term q

def treeToList : CoefficientTree → CoefficientList → CoefficientList
  | .empty, q => q
  | .leaf k c, q => (k, c) :: q
  | .node p q, r => treeToList p (treeToList q r)

theorem coefficientEval_treeToList {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) (p : CoefficientTree) (q : CoefficientList) :
    coefficientEval term (treeToList p q) = treeEval term p + coefficientEval term q := by
  induction p generalizing q with
  | empty => simp [treeToList, treeEval]
  | leaf k c => rfl
  | node p q ihp ihq =>
      simp only [treeToList, treeEval, ihp, ihq, add_assoc]

theorem treeEval_eq_coefficientEval {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) (p : CoefficientTree) :
    treeEval term p = coefficientEval term (treeToList p []) := by
  simpa [coefficientEval] using (coefficientEval_treeToList term p []).symm

theorem treeEval_merge {R : Type*} [CommRing R]
    (x y : Fin 16 → R) (p q r : CoefficientTree)
    (h : coefficientMerge (treeToList p []) (treeToList q []) = treeToList r []) :
    treeEval (monomialTerm x y) p + treeEval (monomialTerm x y) q =
      treeEval (monomialTerm x y) r := by
  simp only [treeEval_eq_coefficientEval]
  rw [← coefficientEval_merge (monomialTerm x y) (monomialTerm_zero x y)
    (monomialTerm_add x y), h]

end HS.CertificateParts
