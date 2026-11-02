import Std

/-!
# Finite block accounting and the sharp reduced-kernel bound

This file formalizes the incidence-counting and extremal-arithmetic part of the
block reduction. It does not formalize graph shortest paths, the block-cut-tree
construction, or the distance-based proof that the graph's boundary supplies
these accounting data. Those graph-theoretic inputs are proved in the manuscript.

There are no `sorry`, `admit`, or declared axioms. All results below are ordinary
conditional theorems or consequences of the concrete structures defined here.
-/

namespace HarmonicBoundary

private def bit : Bool → Nat
  | false => 0
  | true => 1

private def countTrue : List Bool → Nat
  | [] => 0
  | b :: bs => bit b + countTrue bs

private theorem countTrue_le_length (bs : List Bool) :
    countTrue bs ≤ bs.length := by
  induction bs with
  | nil => simp [countTrue]
  | cons b bs ih =>
    cases b <;> simp [countTrue, bit] at * <;> omega

/-- Boundary incidences at one cut vertex. Its incident block-boundary flags
are explicit finite data; at least two blocks meet at a cut vertex. -/
structure CutProfile where
  localBoundary : List Bool
  atLeastTwo : 2 ≤ localBoundary.length
  globalBoundary : Bool

def CutProfile.incidence (p : CutProfile) : Nat := p.localBoundary.length

def CutProfile.localCount (p : CutProfile) : Nat := countTrue p.localBoundary

def CutProfile.globalCount (p : CutProfile) : Nat := bit p.globalBoundary

def CutProfile.treeCharge (p : CutProfile) : Nat := p.incidence - 1

/-- The exact nonnegative defect of a cut vertex. -/
def CutProfile.defect (p : CutProfile) : Nat :=
  2 * p.treeCharge + p.globalCount - p.localCount

theorem CutProfile.localCount_le_incidence (p : CutProfile) :
    p.localCount ≤ p.incidence := by
  exact countTrue_le_length p.localBoundary

theorem CutProfile.incidence_ge_two (p : CutProfile) :
    2 ≤ p.incidence := p.atLeastTwo

theorem CutProfile.defect_identity (p : CutProfile) :
    p.defect + p.localCount = 2 * p.treeCharge + p.globalCount := by
  have hc := p.localCount_le_incidence
  have ht := p.incidence_ge_two
  unfold CutProfile.defect CutProfile.treeCharge
  omega

theorem CutProfile.defect_lower_bound (p : CutProfile) :
    p.incidence - 2 ≤ p.defect := by
  have hc := p.localCount_le_incidence
  have ht := p.incidence_ge_two
  have he := p.defect_identity
  unfold CutProfile.treeCharge at he
  omega

/-- Intrinsic boundary count of one nontrivial block. The lower bound is the
known two-boundary-vertex theorem, supplied at the block level. -/
structure BlockProfile where
  boundaryCount : Nat
  atLeastTwo : 2 ≤ boundaryCount

def BlockProfile.excess (b : BlockProfile) : Nat := b.boundaryCount - 2

private def totalBoundary : List BlockProfile → Nat
  | [] => 0
  | b :: bs => b.boundaryCount + totalBoundary bs

private def totalExcess : List BlockProfile → Nat
  | [] => 0
  | b :: bs => b.excess + totalExcess bs

private def totalLocal : List CutProfile → Nat
  | [] => 0
  | p :: ps => p.localCount + totalLocal ps

private def totalGlobal : List CutProfile → Nat
  | [] => 0
  | p :: ps => p.globalCount + totalGlobal ps

private def totalTreeCharge : List CutProfile → Nat
  | [] => 0
  | p :: ps => p.treeCharge + totalTreeCharge ps

private def totalDefect : List CutProfile → Nat
  | [] => 0
  | p :: ps => p.defect + totalDefect ps

private theorem boundary_sum_decomposition (bs : List BlockProfile) :
    totalBoundary bs = totalExcess bs + 2 * bs.length := by
  induction bs with
  | nil => simp [totalBoundary, totalExcess]
  | cons b bs ih =>
    have hb := b.atLeastTwo
    simp only [totalBoundary, totalExcess, List.length_cons]
    unfold BlockProfile.excess
    omega

private theorem defect_sum_identity (ps : List CutProfile) :
    totalDefect ps + totalLocal ps =
      2 * totalTreeCharge ps + totalGlobal ps := by
  induction ps with
  | nil => simp [totalDefect, totalLocal, totalTreeCharge, totalGlobal]
  | cons p ps ih =>
    have hp := p.defect_identity
    simp only [totalDefect, totalLocal, totalTreeCharge, totalGlobal]
    omega

/-- The finite counting interface proved by the block decomposition in the
manuscript. `boundaryConservation` is the actual membership double count;
`treeIdentity` is the Euler identity of the block-cut tree. -/
structure BlockAccounting where
  blocks : List BlockProfile
  cuts : List CutProfile
  boundary : Nat
  treeIdentity : totalTreeCharge cuts + 1 = blocks.length
  boundaryConservation :
    boundary + totalLocal cuts = totalBoundary blocks + totalGlobal cuts

/-- Exact defect budget, from finite boundary incidence and tree counting. -/
theorem exact_block_budget (a : BlockAccounting) :
    a.boundary = 2 + totalExcess a.blocks + totalDefect a.cuts := by
  have hb := boundary_sum_decomposition a.blocks
  have hc := defect_sum_identity a.cuts
  have ht := a.treeIdentity
  have hm := a.boundaryConservation
  omega

/-- All quantities used in the reduced-graph vertex count, including intrinsic
block interiors `interiors`. These are counts, not graph axioms. -/
structure KernelAccounting where
  boundary : Nat
  nonbridgeBlocks : Nat
  blockExcess : Nat
  cutDefect : Nat
  interiors : Nat
  blockVertices : Nat
  bridgeBranches : Nat
  leaves : Nat
  order : Nat
  exactBudget : boundary = 2 + blockExcess + cutDefect
  blocksConsumeBudget : nonbridgeBlocks ≤ blockExcess
  blockVertexBound : blockVertices ≤ blockExcess + 2 * nonbridgeBlocks + interiors
  branchBound : bridgeBranches ≤ cutDefect
  leafBound : leaves ≤ boundary
  vertexPartition : order = blockVertices + bridgeBranches + leaves

/-- The sharper universal bound retaining the number of non-bridge blocks. -/
theorem universal_kernel_bound_refined (a : KernelAccounting) :
    a.order + 2 ≤ 2 * a.boundary + 2 * a.nonbridgeBlocks + a.interiors := by
  have h1 := a.exactBudget
  have h2 := a.blockVertexBound
  have h3 := a.branchBound
  have h4 := a.leafBound
  have h5 := a.vertexPartition
  omega

/-- The universal bound with the sole additional parameter being the sum of
intrinsic block interiors. -/
theorem universal_kernel_bound (a : KernelAccounting) :
    a.order + 6 ≤ 4 * a.boundary + a.interiors := by
  have h1 := universal_kernel_bound_refined a
  have h2 := a.exactBudget
  have h3 := a.blocksConsumeBudget
  omega

/-- Sharp finite kernel bound whenever every block consists entirely of its
intrinsic boundary. This is the numeric conclusion of the graph theorem. -/
theorem full_block_kernel_bound (a : KernelAccounting) (hi : a.interiors = 0) :
    a.order ≤ 4 * a.boundary - 6 := by
  have h := universal_kernel_bound a
  omega

/-- In particular the reduced kernel has at most fourteen vertices when it
has five boundary vertices and its blocks have no intrinsic interior. -/
theorem five_boundary_kernel_bound (a : KernelAccounting)
    (hi : a.interiors = 0) (hk : a.boundary = 5) :
    a.order ≤ 14 := by
  have h := full_block_kernel_bound a hi
  omega

/-- When each intrinsic block interior also consumes one unit of excess
budget, the interior penalty reverses sign. The manuscript proves this
additional input for the diameter-two-or-cycle block class. -/
theorem compensated_interior_kernel_bound (a : KernelAccounting)
    (hc : a.nonbridgeBlocks + a.interiors ≤ a.blockExcess) :
    a.order + 6 + a.interiors ≤ 4 * a.boundary := by
  have h1 := universal_kernel_bound_refined a
  have h2 := a.exactBudget
  omega

/-- Diameter-two-or-cycle blocks consequently retain the sharp fourteen
vertex bound at boundary size five. -/
theorem compensated_five_boundary_kernel_bound (a : KernelAccounting)
    (hc : a.nonbridgeBlocks + a.interiors ≤ a.blockExcess)
    (hk : a.boundary = 5) :
    a.order + a.interiors ≤ 14 := by
  have h := compensated_interior_kernel_bound a hc
  omega

/-- Equality forces all of the counting equalities used to derive the
triangle-expanded trivalent-tree classification in the manuscript. -/
theorem full_block_kernel_equality (a : KernelAccounting)
    (hi : a.interiors = 0) (he : a.order + 6 = 4 * a.boundary) :
    a.nonbridgeBlocks + 2 = a.boundary ∧
    a.blockExcess = a.nonbridgeBlocks ∧
    a.cutDefect = 0 ∧
    a.leaves = a.boundary ∧
    a.bridgeBranches = 0 ∧
    a.blockVertices = 3 * a.nonbridgeBlocks := by
  have h1 := a.exactBudget
  have h2 := a.blocksConsumeBudget
  have h3 := a.blockVertexBound
  have h4 := a.branchBound
  have h5 := a.leafBound
  have h6 := a.vertexPartition
  omega

/-- Every number k>=2 attains the arithmetic bound; the manuscript realizes
these data as the explicit triangle expansion of a trivalent tree. -/
def sharpKernelAccounting (k : Nat) (hk : 2 ≤ k) : KernelAccounting where
  boundary := k
  nonbridgeBlocks := k - 2
  blockExcess := k - 2
  cutDefect := 0
  interiors := 0
  blockVertices := 3 * (k - 2)
  bridgeBranches := 0
  leaves := k
  order := 4 * k - 6
  exactBudget := by omega
  blocksConsumeBudget := by omega
  blockVertexBound := by omega
  branchBound := by omega
  leafBound := by omega
  vertexPartition := by omega

theorem sharpKernelAccounting_attains_bound (k : Nat) (hk : 2 ≤ k) :
    (sharpKernelAccounting k hk).order + 6 = 4 * k := by
  simp only [sharpKernelAccounting]
  omega

end HarmonicBoundary
