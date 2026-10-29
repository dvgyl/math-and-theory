import GraphDegree
import Mathlib.Data.Multiset.Filter

noncomputable section
namespace SquareFlowerCompletion.Extremal

def nonzeroRootMultiset (n : ℕ) : Multiset ℂ := by
  classical
  exact (graphPolynomial n).roots.filter (fun z => z ≠ 0)

theorem graph_roots_card (n : ℕ) : (graphPolynomial n).roots.card = 3*n+1 := by
  rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (graphPolynomial n))]
  exact graphPolynomial_natDegree n

theorem mem_nonzeroRootMultiset {n : ℕ} {z : ℂ} :
    z ∈ nonzeroRootMultiset n ↔ z ≠ 0 ∧ (graphPolynomial n).eval z = 0 := by
  classical
  simp [nonzeroRootMultiset,Polynomial.mem_roots (graphPolynomial_ne_zero n),
    Polynomial.IsRoot.def,and_comm]

theorem nonzero_root_multiset_card (n : ℕ) : (nonzeroRootMultiset n).card = 2*n := by
  classical
  have h := congrArg Multiset.card
    (Multiset.filter_add_not (p:=fun z : ℂ => z = 0) (graphPolynomial n).roots)
  have hcard : (n+1)+(nonzeroRootMultiset n).card = 3*n+1 := by
    simpa only [Multiset.card_add,Multiset.filter_eq',Multiset.card_replicate,
      Polynomial.count_roots,graphPolynomial_origin_multiplicity,graph_roots_card,
      nonzeroRootMultiset] using h
  omega

#print axioms graph_roots_card
#print axioms mem_nonzeroRootMultiset
#print axioms nonzero_root_multiset_card
end SquareFlowerCompletion.Extremal
