import OrderedAllocationReduction

set_option format.width 100000

open Finset

namespace OrderedAllocationIndependentAudit

variable {Agent Good : Type*}
variable [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
variable [Fintype Good] [DecidableEq Good]

/-- The exact transfer with utility, recipient counts, and extra copies expanded. -/
theorem exact_transfer_expanded
    (A : Agent → Finset (Fin (Fintype.card Good)))
    (rank : Agent → Good ≃ Fin (Fintype.card Good))
    (v : Agent → Good → ℝ)
    (hnonneg : ∀ i g, 0 ≤ v i g)
    (hordered : ∀ i (a b : Fin (Fintype.card Good)), a ≤ b →
      v i ((rank i).symm b) ≤ v i ((rank i).symm a))
    (k : ℕ)
    (hpergood : ∀ j, (univ.filter (fun i => j ∈ A i)).card - 1 ≤ k) :
    ∃ B : Agent → Finset Good,
      (∀ i, (∑ j ∈ A i, v i ((rank i).symm j)) ≤ ∑ g ∈ B i, v i g) ∧
      (∑ g : Good, ((univ.filter (fun i => g ∈ B i)).card - 1)) =
        ∑ j : Fin (Fintype.card Good), ((univ.filter (fun i => j ∈ A i)).card - 1) ∧
      (∀ g, (univ.filter (fun i => g ∈ B i)).card - 1 ≤ k) ∧
      ∀ g, 1 ≤ (univ.filter (fun i => g ∈ B i)).card := by
  have hsorted : ∀ i, Antitone (fun j => v i ((rank i).symm j)) := by
    intro i a b hab
    exact hordered i a b hab
  simpa only [OrderedReductionCompletion.utility,
    OrderedReductionCompletion.totalCopies, OrderedReductionCompletion.extraCopies,
    OrderedReductionCompletion.multiplicity] using
    (OrderedReductionAllocation.ordered_allocation_transfer_exact
      A rank v hnonneg hsorted k hpergood)

end OrderedAllocationIndependentAudit

#print axioms OrderedReductionAllocation.ordered_allocation_transfer_exact
#print axioms OrderedReductionAllocation.ordered_allocation_transfer
#print axioms OrderedReductionAllocation.ordered_threshold_transfer
#print axioms OrderedAllocationIndependentAudit.exact_transfer_expanded
