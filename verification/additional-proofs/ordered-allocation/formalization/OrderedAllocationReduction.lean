import Mathlib.Tactic
import Mathlib.Combinatorics.Hall.Finite

/-!
# General ordered-instance reduction with copies

Complete mathematical proof and Lean formalization, constructed 2026-10-28.

## Result and source-comparison limits

This file proves the self-contained ordered-allocation transfer theorem below.
The motivating attribution to Akrami et al., arXiv:2502.09377v3, is supplied
source context. The literal source definitions, restricted theorem, question,
and current version have not been verified. No external question resolution,
verified strengthening, or first priority is claimed. The local definitions
and the formal theorem determine the precise scope.

## Precise statement

Let N be a nonempty finite set of agents and M a finite set of m goods.
Agent i has nonnegative weights v_i(g). Let r_i:M -> {1,...,m} be a bijection
sorting these weights in decreasing order, and put w_i(j)=v_i(r_i^{-1}(j)).

An ordered allocation is an arbitrary family A_i subset {1,...,m}.
For any allocation X, define:
  multiplicity_X(g) = number of agents i with g in X_i;
  extra_X(g) = max(0, multiplicity_X(g)-1);
  copies(X) = sum_g extra_X(g).

If extra_A(j)<=k for all j, there exist sets B_i subset M satisfying:
  sum_{g in B_i} v_i(g) >= sum_{j in A_i} w_i(j), for every agent i;
  copies(B) = copies(A);
  extra_B(g) <= k, for every good g;
  multiplicity_B(g) >= 1, for every good g.

Thus every ordered (t,k)-allocation transfers with both budgets intact.
Any attained vector of utility thresholds transfers as well.

The construction may change which goods are copied. Completion can increase
an agent's original bundle size; that size is not asserted to be preserved.
The theorem concerns goods with nonnegative additive valuations.

The mathematics below uses ranks 1,...,m; Lean's Fin m is zero-based.

## Complete proof

1. Complete the input.

Give every unused virtual good once to a fixed agent. Nonnegative weights
ensure that utilities cannot decrease. An unused good changes multiplicity
from zero to one, leaving its extra-copy count zero. Write C for the completed
allocation, D=sum_i |C_i|, and q=k+1. Then every rank occurs between one and q
times, so m<=D<=qm and D-m=copies(C)=copies(A).

2. The counting inequality.

Create a slot (i,a) for each a in C_i. An incidence (i,g) is eligible for that
slot when r_i(g)<=a. For a set P of slots write N(P) for its eligible
agent-good incidences. Given any incidence set I, put S=projection_good(I)
and s=|S|. Let c(s) be the number of ALL slots of rank at most s.

We claim:
  |P| <= |N(P)\I| + c(s).                                      (1)

At most c(s) selected slots have rank at most s. For each agent with a selected
higher-rank slot, let a be that agent's largest selected rank. Distinctness of
the agent's requested ranks bounds its selected higher-rank slots by a-s.
Among the agent's top a real goods, at least a-s lie outside S. Their incidences
belong to N(P)\I. Incidences belonging to different agents are distinct, so
the number of higher-rank slots is at most |N(P)\I|, proving (1).

The global rank multiplicities give:
  c(s) <= qs;
  c(s) <= D-m+s.                                               (2)
The second bound follows because each of the last m-s ranks occurs at least once.

3. Balanced bipartite matching graph.

Left vertices:
  D requested slots;
  one left port for each of the nm agent-good incidences;
  qm-D dummy vertices.

Right vertices:
  one right port for each of the nm agent-good incidences;
  one primary copy of each good;
  q-1 secondary copies of each good.

Both sides have nm+qm vertices. Edges:
  a slot connects to all its eligible right ports;
  left port (i,g) connects to its identical right port and all q copies of g;
  each dummy connects to every secondary copy.

Consider an arbitrary subset of the left vertices, with slot part P, port
part I, and dummy part T. Put S=projection_good(I), s=|S|.

If T is empty, its neighbors contain N(P) union I and all q copies of S.
These are distinct vertex classes, giving at least
  |I|+|N(P)\I|+qs >= |I|+|P|
neighbors by (1) and the first bound in (2).

If T is nonempty, its neighbors contain N(P) union I, all (q-1)m secondary
copies, and the s primary copies from S. There are at least
  |I|+|N(P)\I|+(q-1)m+s
neighbors. By (1), (2), and |T|<=qm-D,
  |P|+|T| <= |N(P)\I|+(D-m+s)+(qm-D)
            = |N(P)\I|+(q-1)m+s.
Adding |I| proves Hall's condition in this case too.

Hall's marriage theorem gives a perfect matching.

4. Extract an allocation.

Each slot matches to an eligible right port (i,g); assign g to agent i.
Distinct slots match distinct ports, so an agent cannot receive a good twice.

When a slot uses right port (i,g), the matching cannot use that port's identity
edge. Its left port must match one of g's q copies. Distinct assigned incidences
use distinct copy vertices, proving multiplicity at most q.

Every primary copy of g is matched from a left port (i,g), since slots and
dummies have no edges to primaries. This left port is already occupied, so
its right port must be matched from a slot. Thus every good is used at least once.

All D slots are filled. Coverage gives copies(B)=D-m=copies(A), and the upper
multiplicity bound gives extra_B(g)<=q-1=k. Eligibility ensures that each filled
slot provides at least its requested ordered value. Sum within each agent's
bundle and then use the utility increase from completion. This proves the theorem.

## Algorithm and verification scope

The graph is explicit and bipartite maximum matching finds the allocation.
For a polynomial-size implementation, use q=min(k+1,n): bundles are sets, so
no good occurs more than n times. Each side then has at most 2nm vertices and
a crude edge bound is O(n^2 m^2). Standard bipartite matching gives a
polynomial-time transformation even for binary-encoded large k.

Lean verifies the universal existence theorem, rank eligibility, set-valued
allocation, utilities, exact total extra-copy preservation, per-good cap, and
the treatment of unused goods. It does not formalize the runtime analysis of
an executable matching implementation. That algorithmic conclusion is the
standard consequence of the explicit polynomial-size graph.

This solves the general ordered-instance reduction question. It does not solve
the separate conjecture that one extra good always suffices for exact MMS.

## Reproduction

Lean 4.19.0, commit 6caaee842e94.
Mathlib v4.19.0, commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
The mathlib checkout used for verification had no source modifications.

This source is self-contained apart from Mathlib. It imports no generated
local proof modules. In a mathlib checkout at the pinned revision, run:
  lake exe cache get
  lake env lean OrderedAllocationReduction.lean

Main checked declarations:
  OrderedReductionAllocation.ordered_allocation_transfer_exact
  OrderedReductionAllocation.ordered_allocation_transfer
  OrderedReductionAllocation.ordered_threshold_transfer

The final axiom checks report only propext, Classical.choice, Quot.sound,
the standard logical foundations used by mathlib. No target theorem,
feasibility assertion, or computation oracle is assumed.
-/



/-! ## Formal module: Basic -/

namespace OrderedReduction

open Finset

variable {Agent Good Slot : Type*}

def prefixSlots [Fintype Slot] (pos : Slot → Fin m) (k : ℕ) : Finset Slot :=
  Finset.univ.filter (fun s => (pos s).val < k)

def neighbors [Fintype Agent] [Fintype Good] [DecidableEq Agent]
    (owner : Slot → Agent) (pos : Slot → Fin m)
    (rank : Agent → Good ≃ Fin m) (s : Slot) : Finset (Agent × Good) :=
  Finset.univ.filter (fun p => p.1 = owner s ∧ rank (owner s) p.2 ≤ pos s)

end OrderedReduction


/-! ## Formal module: Counts -/

namespace OrderedReduction

open Finset

variable {Slot : Type*} [Fintype Slot]

def rankPrefix (m k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => j.val < k)

def slotMultiplicity (pos : Slot → Fin m) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun s => pos s = j)).card

theorem card_rankPrefix {m k : ℕ} (hk : k ≤ m) :
    (rankPrefix m k).card = k := by
  classical
  by_cases hkm : k < m
  · have heq : rankPrefix m k = Finset.Iio (⟨k, hkm⟩ : Fin m) := by
      ext j
      simp [rankPrefix, Fin.lt_def]
    rw [heq, Fin.card_Iio]
  · have hkm' : k = m := by omega
    subst k
    have heq : rankPrefix m m = Finset.univ := by
      ext j
      simp [rankPrefix, j.isLt]
    simp [heq]

theorem prefixSlots_card_sum (pos : Slot → Fin m) (k : ℕ) :
    (prefixSlots pos k).card = ∑ j ∈ rankPrefix m k, slotMultiplicity pos j := by
  classical
  simpa [prefixSlots, rankPrefix, slotMultiplicity] using
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ (rankPrefix m k) pos).symm

theorem slotMultiplicity_sum (pos : Slot → Fin m) :
    ∑ j, slotMultiplicity pos j = Fintype.card Slot := by
  classical
  simpa [slotMultiplicity] using
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ pos)

theorem count_bounds (pos : Slot → Fin m) (q : ℕ)
    (hlo : ∀ j, 1 ≤ slotMultiplicity pos j)
    (hhi : ∀ j, slotMultiplicity pos j ≤ q) :
    m ≤ Fintype.card Slot ∧ Fintype.card Slot ≤ q * m := by
  classical
  have hl := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (f := fun _ => 1) (g := slotMultiplicity pos) (fun j _ => hlo j)
  have hu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (f := slotMultiplicity pos) (g := fun _ => q) (fun j _ => hhi j)
  simpa [slotMultiplicity_sum, Nat.mul_comm] using And.intro hl hu

theorem prefixSlots_card_bounds (pos : Slot → Fin m) (q k : ℕ)
    (hk : k ≤ m)
    (hlo : ∀ j, 1 ≤ slotMultiplicity pos j)
    (hhi : ∀ j, slotMultiplicity pos j ≤ q) :
    (prefixSlots pos k).card ≤
      min (q * k) (k + (Fintype.card Slot - m)) := by
  classical
  have htotal := (count_bounds pos q hlo hhi).1
  have hupper := Finset.sum_le_sum (s := rankPrefix m k)
    (f := slotMultiplicity pos) (g := fun _ => q) (fun j _ => hhi j)
  have hp : (prefixSlots pos k).card ≤ q * k := by
    simpa [← prefixSlots_card_sum, card_rankPrefix hk, Nat.mul_comm] using hupper
  have hcomp := Finset.sum_le_sum (s := (rankPrefix m k)ᶜ)
    (f := fun _ => 1) (g := slotMultiplicity pos) (fun j _ => hlo j)
  have hcomp' : m - k ≤ ∑ j ∈ (rankPrefix m k)ᶜ, slotMultiplicity pos j := by
    simpa [Finset.card_compl, card_rankPrefix hk] using hcomp
  have hsplit := Finset.sum_add_sum_compl (rankPrefix m k) (slotMultiplicity pos)
  rw [← prefixSlots_card_sum, slotMultiplicity_sum] at hsplit
  apply le_min hp
  omega


end OrderedReduction


/-! ## Formal module: RankCount -/

namespace OrderedReduction

open Finset

variable {Agent Good Slot : Type*} {m : ℕ}

lemma high_fiber_card_le [Fintype Agent] [Fintype Good] [Fintype Slot]
    [DecidableEq Agent] [DecidableEq Good] [DecidableEq Slot]
    (owner : Slot → Agent) (pos : Slot → Fin m)
    (rank : Agent → Good ≃ Fin m)
    (hsep : Function.Injective (fun s => (owner s, pos s)))
    (P : Finset Slot) (I : Finset (Agent × Good)) (i : Agent) :
    ((P.filter (fun s => (I.image Prod.snd).card ≤ (pos s).val)).filter
      (fun s => owner s = i)).card ≤
    (((P.biUnion (neighbors owner pos rank)) \ I).filter
      (fun p => p.1 = i)).card := by
  classical
  let S : Finset Good := I.image Prod.snd
  let H : Finset Slot := (P.filter (fun s => S.card ≤ (pos s).val)).filter
    (fun s => owner s = i)
  let Q : Finset (Agent × Good) :=
    ((P.biUnion (neighbors owner pos rank)) \ I).filter (fun p => p.1 = i)
  change H.card ≤ Q.card
  by_cases hH : H.Nonempty
  · obtain ⟨x, hx, hmax⟩ := H.exists_max_image (fun s => (pos s).val) hH
    have hxP : x ∈ P := (mem_filter.mp (mem_filter.mp hx).1).1
    have hxi : owner x = i := (mem_filter.mp hx).2
    have hsmall : H.card ≤ (pos x).val + 1 - S.card := by
      calc
        H.card ≤ (Finset.Ico S.card ((pos x).val + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun s => (pos s).val)
          · intro s hs
            exact mem_Ico.mpr ⟨(mem_filter.mp (mem_filter.mp hs).1).2,
              Nat.lt_succ_of_le (hmax s hs)⟩
          · intro s hs t ht hst
            apply hsep
            apply Prod.ext
            · exact (mem_filter.mp hs).2.trans (mem_filter.mp ht).2.symm
            · exact Fin.ext hst
        _ = (pos x).val + 1 - S.card := Nat.card_Ico _ _
    let T : Finset Good := (Finset.Iic (pos x)).map (rank i).symm.toEmbedding
    have hTcard : T.card = (pos x).val + 1 := by
      simp [T, Fin.card_Iic]
    have hTmem (g : Good) : g ∈ T ↔ rank i g ≤ pos x := by
      simp [T]
    have hresid : (T \ S).card ≤ Q.card := by
      apply Finset.card_le_card_of_injOn (fun g => (i, g))
      · intro g hg
        have hgT : g ∈ T := (mem_sdiff.mp hg).1
        have hgS : g ∉ S := (mem_sdiff.mp hg).2
        apply mem_filter.mpr
        refine ⟨mem_sdiff.mpr ⟨?_, ?_⟩, rfl⟩
        · apply mem_biUnion.mpr
          refine ⟨x, hxP, ?_⟩
          simp only [neighbors, mem_filter, mem_univ, true_and]
          exact ⟨hxi.symm, by simpa only [hxi] using (hTmem g).mp hgT⟩
        · intro hig
          exact hgS (Finset.mem_image_of_mem Prod.snd hig)
      · intro g _ h _ hgh
        exact congrArg Prod.snd hgh
    have hTbound : T.card ≤ (T \ S).card + S.card :=
      Finset.card_le_card_sdiff_add_card
    omega
  · have : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    simp [this]

theorem rank_count [Fintype Agent] [Fintype Good] [Fintype Slot]
    [DecidableEq Agent] [DecidableEq Good] [DecidableEq Slot]
    (owner : Slot → Agent) (pos : Slot → Fin m)
    (rank : Agent → Good ≃ Fin m)
    (hsep : Function.Injective (fun s => (owner s, pos s)))
    (P : Finset Slot) (I : Finset (Agent × Good)) :
    P.card ≤ ((P.biUnion (neighbors owner pos rank)) \ I).card +
      (prefixSlots pos (I.image Prod.snd).card).card := by
  classical
  let H := P.filter (fun s => (I.image Prod.snd).card ≤ (pos s).val)
  let L := P.filter (fun s => (pos s).val < (I.image Prod.snd).card)
  let Q := (P.biUnion (neighbors owner pos rank)) \ I
  have hH : H.card ≤ Q.card := by
    calc
      H.card = ∑ i : Agent, (H.filter (fun s => owner s = i)).card := by
        exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ ≤ ∑ i : Agent, (Q.filter (fun p => p.1 = i)).card := by
        apply Finset.sum_le_sum
        intro i _
        exact high_fiber_card_le owner pos rank hsep P I i
      _ = Q.card := by
        symm
        exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hL : L.card ≤ (prefixSlots pos (I.image Prod.snd).card).card := by
    apply Finset.card_le_card
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩
  have hsum : L.card + H.card = P.card := by
    simpa only [L, H, not_lt] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := P) (fun s => (pos s).val < (I.image Prod.snd).card))
  change P.card ≤ Q.card + (prefixSlots pos (I.image Prod.snd).card).card
  omega

end OrderedReduction


/-! ## Formal module: HallGadget -/

/-!
A finite Hall gadget for choosing distinct agent--good incidences while using
every good between one and `k` times.  The distinguished copy of each good is
separate from its `k - 1` secondary copies.
-/

namespace OrderedReduction.HallGadget

open Finset Function

set_option maxHeartbeats 1000000

variable {Slot Agent Good : Type*}
variable [Fintype Slot] [Fintype Agent] [Fintype Good]
variable [DecidableEq Agent] [DecidableEq Good]

abbrev Left (Slot Agent Good : Type*) [Fintype Slot] [Fintype Good] (k : ℕ) :=
  Slot ⊕ ((Agent × Good) ⊕ Fin (k * Fintype.card Good - Fintype.card Slot))

abbrev Copies (Good : Type*) (k : ℕ) := Good ⊕ (Good × Fin (k - 1))

abbrev Right (Agent Good : Type*) (k : ℕ) :=
  (Agent × Good) ⊕ Copies Good k

/-- The three layers of the capacitated matching gadget. -/
def Edge (k : ℕ) (R : Slot → Agent × Good → Prop) :
    Left Slot Agent Good k → Right Agent Good k → Prop
  | .inl s, .inl e => R s e
  | .inr (.inl e), .inl e' => e = e'
  | .inr (.inl e), .inr (.inl g) => e.2 = g
  | .inr (.inl e), .inr (.inr gj) => e.2 = gj.1
  | .inr (.inr _), .inr (.inr _) => True
  | _, _ => False

noncomputable def slotNeighbors (R : Slot → Agent × Good → Prop)
    (P : Finset Slot) : Finset (Agent × Good) := by
  classical
  exact P.biUnion fun s => univ.filter (R s)

/-- A cut condition sufficient for a bijective matching of the entire gadget. -/
theorem exists_bijective_gadget (k : ℕ) (hk : 1 ≤ k)
    (R : Slot → Agent × Good → Prop)
    (hlo : Fintype.card Good ≤ Fintype.card Slot)
    (hhi : Fintype.card Slot ≤ k * Fintype.card Good)
    (hcut : ∀ (P : Finset Slot) (I : Finset (Agent × Good)),
      P.card ≤ (slotNeighbors R P \ I).card +
        min (k * (I.image Prod.snd).card)
          ((I.image Prod.snd).card + (Fintype.card Slot - Fintype.card Good))) :
    ∃ f : Left Slot Agent Good k → Right Agent Good k,
      Bijective f ∧ ∀ x, Edge k R x (f x) := by
  classical
  let t : Left Slot Agent Good k → Finset (Right Agent Good k) :=
    fun x => univ.filter (Edge k R x)
  have hall : ∀ A : Finset (Left Slot Agent Good k), A.card ≤ (A.biUnion t).card := by
    intro A
    let P : Finset Slot := A.toLeft
    let I : Finset (Agent × Good) := A.toRight.toLeft
    let T : Finset (Fin (k * Fintype.card Good - Fintype.card Slot)) :=
      A.toRight.toRight
    let U : Finset Good := I.image Prod.snd
    let J : Finset (Agent × Good) := slotNeighbors R P ∪ I
    have hcardA : A.card = P.card + I.card + T.card := by
      have h₁ := Finset.card_toLeft_add_card_toRight (u := A)
      have h₂ := Finset.card_toLeft_add_card_toRight (u := A.toRight)
      dsimp [P, I, T]
      omega
    have hcardJ : J.card = (slotNeighbors R P \ I).card + I.card := by
      exact (Finset.card_sdiff_add_card _ _).symm
    have hJ : ∀ e ∈ J, Sum.inl e ∈ A.biUnion t := by
      intro e he
      rcases Finset.mem_union.mp he with hN | hI
      · rcases Finset.mem_biUnion.mp hN with ⟨s, hs, hse⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨Sum.inl s, ?_, ?_⟩
        · simpa [P] using hs
        · simpa [t, Edge] using hse
      · apply Finset.mem_biUnion.mpr
        refine ⟨Sum.inr (Sum.inl e), ?_, ?_⟩
        · simpa [I] using hI
        · simp [t, Edge]
    have hprimary : ∀ g ∈ U, Sum.inr (Sum.inl g) ∈ A.biUnion t := by
      intro g hg
      rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨Sum.inr (Sum.inl e), ?_, ?_⟩
      · simpa [I] using he
      · simp [t, Edge]
    have hsecondary : ∀ g ∈ U, ∀ j : Fin (k - 1),
        Sum.inr (Sum.inr (g, j)) ∈ A.biUnion t := by
      intro g hg j
      rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨Sum.inr (Sum.inl e), ?_, ?_⟩
      · simpa [I] using he
      · simp [t, Edge]
    have hc := hcut P I
    change P.card ≤ (slotNeighbors R P \ I).card +
      min (k * U.card) (U.card + (Fintype.card Slot - Fintype.card Good)) at hc
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    by_cases hT : T = ∅
    · let V : Finset (Copies Good k) := U.disjSum (U ×ˢ (univ : Finset (Fin (k - 1))))
      have hsub : J.disjSum V ⊆ A.biUnion t := by
        intro x hx
        rcases x with e | (g | ⟨g, j⟩)
        · exact hJ e (by simpa using hx)
        · exact hprimary g (by simpa [V] using hx)
        · exact hsecondary g (by simpa [V] using hx) j
      have hbound := Finset.card_le_card hsub
      have hcardV : V.card = k * U.card := by
        simp only [V, Finset.card_disjSum, Finset.card_product, Finset.card_univ,
          Fintype.card_fin]
        calc
          U.card + U.card * (k - 1) = U.card * (k - 1 + 1) := by ring
          _ = k * U.card := by rw [hk', Nat.mul_comm]
      rw [Finset.card_disjSum, hcardJ, hcardV] at hbound
      have hTc : T.card = 0 := by simp [hT]
      have hmin := min_le_left (k * U.card)
        (U.card + (Fintype.card Slot - Fintype.card Good))
      omega
    · let V : Finset (Copies Good k) :=
        U.disjSum ((univ : Finset Good) ×ˢ (univ : Finset (Fin (k - 1))))
      obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hT
      have hsub : J.disjSum V ⊆ A.biUnion t := by
        intro x hx
        rcases x with e | (g | ⟨g, j⟩)
        · exact hJ e (by simpa using hx)
        · exact hprimary g (by simpa [V] using hx)
        · apply Finset.mem_biUnion.mpr
          refine ⟨Sum.inr (Sum.inr d), ?_, ?_⟩
          · simpa [T] using hd
          · simp [t, Edge]
      have hbound := Finset.card_le_card hsub
      have hcardV : V.card = U.card + Fintype.card Good * (k - 1) := by
        simp [V]
      rw [Finset.card_disjSum, hcardJ, hcardV] at hbound
      have hTc : T.card ≤ k * Fintype.card Good - Fintype.card Slot := by
        simpa using Finset.card_le_univ T
      have hmin := min_le_right (k * U.card)
        (U.card + (Fintype.card Slot - Fintype.card Good))
      have hmul : Fintype.card Good * (k - 1) + Fintype.card Good =
          k * Fintype.card Good := by
        calc
          _ = Fintype.card Good * (k - 1 + 1) := by ring
          _ = _ := by rw [hk', Nat.mul_comm]
      omega
  obtain ⟨f, hf, hft⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  refine ⟨f, ?_, ?_⟩
  · apply (Fintype.bijective_iff_injective_and_card f).mpr
    refine ⟨hf, ?_⟩
    simp only [Left, Right, Copies, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hmul : Fintype.card Good * (k - 1) + Fintype.card Good =
        k * Fintype.card Good := by
      calc
        _ = Fintype.card Good * (k - 1 + 1) := by ring
        _ = _ := by rw [hk', Nat.mul_comm]
    omega
  · intro x
    exact (Finset.mem_filter.mp (hft x)).2

end OrderedReduction.HallGadget


/-! ## Formal module: Extraction -/

namespace OrderedReduction.HallGadget

open Finset Function

variable {Slot Agent Good : Type*}
variable [Fintype Slot] [Fintype Agent] [Fintype Good]
variable [DecidableEq Agent] [DecidableEq Good]

omit [Fintype Agent] [DecidableEq Agent] in
/-- A bijective matching in the gadget gives a set-valued assignment with
    at least one and at most `k` recipients for every good. -/
theorem exists_assignment_of_bijective_gadget (k : ℕ) (hk : 1 ≤ k)
    (R : Slot → Agent × Good → Prop)
    (f : Left Slot Agent Good k → Right Agent Good k)
    (hf : Bijective f) (hedge : ∀ x, Edge k R x (f x)) :
    ∃ a : Slot → Agent × Good,
      Injective a ∧ (∀ s, R s (a s)) ∧
      ∀ g, 1 ≤ (univ.filter (fun s => (a s).2 = g)).card ∧
        (univ.filter (fun s => (a s).2 = g)).card ≤ k := by
  classical
  have hslot (s : Slot) : ∃ e, f (Sum.inl s) = Sum.inl e ∧ R s e := by
    have he := hedge (Sum.inl s)
    cases h : f (Sum.inl s) with
    | inl e => exact ⟨e, rfl, by simpa [Edge, h] using he⟩
    | inr c => simp [Edge, h] at he
  choose a ha har using hslot
  have hinj : Injective a := by
    intro s t hst
    have hft : f (Sum.inl s) = f (Sum.inl t) := by rw [ha s, ha t, hst]
    exact Sum.inl.inj (hf.1 hft)
  have hport_not_incidence (s : Slot) (e : Agent × Good) :
      f (Sum.inr (Sum.inl (a s))) ≠ Sum.inl e := by
    intro h
    have he : a s = e := by
      simpa [Edge, h] using hedge (Sum.inr (Sum.inl (a s)))
    have hft : f (Sum.inr (Sum.inl (a s))) = f (Sum.inl s) := by
      rw [h, ha s, he]
    exact Sum.noConfusion (hf.1 hft)
  have hcover (g : Good) : ∃ s, (a s).2 = g := by
    obtain ⟨x, hx⟩ := hf.2 (Sum.inr (Sum.inl g))
    have hprimary : ∃ e : Agent × Good,
        f (Sum.inr (Sum.inl e)) = Sum.inr (Sum.inl g) ∧ e.2 = g := by
      have he := hedge x
      cases x with
      | inl s => simp [Edge, hx] at he
      | inr y =>
        cases y with
        | inl e => exact ⟨e, hx, by simpa [Edge, hx] using he⟩
        | inr d => simp [Edge, hx] at he
    obtain ⟨e, hemap, heg⟩ := hprimary
    obtain ⟨y, hy⟩ := hf.2 (Sum.inl e)
    have hyedge := hedge y
    cases y with
    | inl s =>
      refine ⟨s, ?_⟩
      have hase : a s = e := Sum.inl.inj ((ha s).symm.trans hy)
      simpa only [hase] using heg
    | inr z =>
      cases z with
      | inl e' =>
        have he'e : e' = e := by simpa [Edge, hy] using hyedge
        subst e'
        have hcontra := hemap.symm.trans hy
        exact Sum.noConfusion hcontra
      | inr d => simp [Edge, hy] at hyedge
  refine ⟨a, hinj, har, ?_⟩
  intro g
  constructor
  · obtain ⟨s, hs⟩ := hcover g
    exact Finset.card_pos.mpr ⟨s, by simp [hs]⟩
  · let U : Finset (Copies Good k) :=
      ({g} : Finset Good).disjSum ({g} ×ˢ (univ : Finset (Fin (k - 1))))
    let V : Finset (Right Agent Good k) :=
      U.map ⟨Sum.inr, Sum.inr_injective⟩
    have hVcard : V.card = k := by
      simp only [V, Finset.card_map, U, Finset.card_disjSum, Finset.card_product,
        Finset.card_singleton, Finset.card_univ, Fintype.card_fin, one_mul]
      omega
    calc
      (univ.filter (fun s => (a s).2 = g)).card ≤ V.card := by
        apply Finset.card_le_card_of_injOn
          (fun s => f (Sum.inr (Sum.inl (a s))))
        · intro s hs
          have hsg : (a s).2 = g := (Finset.mem_filter.mp hs).2
          have he := hedge (Sum.inr (Sum.inl (a s)))
          cases h : f (Sum.inr (Sum.inl (a s))) with
          | inl e => exact False.elim (hport_not_incidence s e h)
          | inr c =>
            cases c with
            | inl g' =>
              have hgg' : (a s).2 = g' := by simpa [Edge, h] using he
              have hg'g : g' = g := hgg'.symm.trans hsg
              simp [V, U, hg'g]
            | inr gj =>
              have hgg' : (a s).2 = gj.1 := by simpa [Edge, h] using he
              have hg'g : gj.1 = g := hgg'.symm.trans hsg
              simp [V, U, hg'g]
              exact ⟨gj.2, Prod.ext hg'g.symm rfl⟩
        · intro s _ t _ hst
          apply hinj
          exact Sum.inl.inj (Sum.inr.inj (hf.1 hst))
      _ = k := hVcard

end OrderedReduction.HallGadget


/-! ## Formal module: Core -/

/-!
# Ordered-to-personal ranking transfer with bounded multiplicities

Every requested slot has an owner and a distinct rank within that owner's
bundle.  If every virtual rank occurs between one and q times, the slots can
be filled with distinct agent--good incidences, using each actual good between
one and q times, and never giving an owner a worse personal rank.
-/

namespace OrderedReduction

open Finset Function

variable {Agent Good Slot : Type*}
variable [Fintype Agent] [Fintype Good] [Fintype Slot]
variable [DecidableEq Agent] [DecidableEq Good] [DecidableEq Slot]

theorem ordered_slots_transfer (q : ℕ) (hq : 1 ≤ q)
    (owner : Slot → Agent) (pos : Slot → Fin (Fintype.card Good))
    (rank : Agent → Good ≃ Fin (Fintype.card Good))
    (hsep : Injective (fun s => (owner s, pos s)))
    (hlo : ∀ j, 1 ≤ slotMultiplicity pos j)
    (hhi : ∀ j, slotMultiplicity pos j ≤ q) :
    ∃ a : Slot → Agent × Good,
      Injective a ∧
      (∀ s, (a s).1 = owner s ∧ rank (owner s) (a s).2 ≤ pos s) ∧
      ∀ g, 1 ≤ (univ.filter (fun s => (a s).2 = g)).card ∧
        (univ.filter (fun s => (a s).2 = g)).card ≤ q := by
  classical
  let R : Slot → Agent × Good → Prop :=
    fun s p => p.1 = owner s ∧ rank (owner s) p.2 ≤ pos s
  have hbounds := count_bounds pos q hlo hhi
  have hcut (P : Finset Slot) (I : Finset (Agent × Good)) :
      P.card ≤ (HallGadget.slotNeighbors R P \ I).card +
        min (q * (I.image Prod.snd).card)
          ((I.image Prod.snd).card + (Fintype.card Slot - Fintype.card Good)) := by
    have hs : (I.image Prod.snd).card ≤ Fintype.card Good := Finset.card_le_univ _
    have hprefix := prefixSlots_card_bounds pos q (I.image Prod.snd).card hs hlo hhi
    have hmain := rank_count owner pos rank hsep P I
    have hN : HallGadget.slotNeighbors R P = P.biUnion (neighbors owner pos rank) := by
      ext p
      simp [HallGadget.slotNeighbors, neighbors, R]
    rw [hN]
    exact hmain.trans (Nat.add_le_add_left hprefix _)
  obtain ⟨f, hf, hedge⟩ := HallGadget.exists_bijective_gadget q hq R
    hbounds.1 hbounds.2 hcut
  exact HallGadget.exists_assignment_of_bijective_gadget q hq R f hf hedge


end OrderedReduction


/-! ## Formal module: Completion -/

/-!
# Completing an allocation without using additional copies

An allocation is a family of sets; goods not allocated to anyone may be given
to a fixed agent.  This does not change either the per-good or the total
number of extra copies.  These lemmas handle the fact that Definition 2.5
of arXiv:2502.09377 permits unallocated goods.
-/

namespace OrderedReductionCompletion

open Finset

variable {Agent Good : Type*} [Fintype Agent] [DecidableEq Agent]
  [Fintype Good] [DecidableEq Good]

def multiplicity (A : Agent → Finset Good) (g : Good) : ℕ :=
  (univ.filter fun i => g ∈ A i).card

def extraCopies (A : Agent → Finset Good) (g : Good) : ℕ :=
  multiplicity A g - 1

def totalCopies (A : Agent → Finset Good) : ℕ :=
  ∑ g, extraCopies A g

def complete (A : Agent → Finset Good) (i₀ : Agent) (i : Agent) : Finset Good :=
  A i ∪ if i = i₀ then univ \ univ.biUnion A else ∅

theorem mem_complete (A : Agent → Finset Good) (i₀ i : Agent) (g : Good) :
    g ∈ complete A i₀ i ↔ g ∈ A i ∨ (i = i₀ ∧ ¬ ∃ j, g ∈ A j) := by
  classical
  by_cases hi : i = i₀ <;> simp [complete, hi]

theorem subset_complete (A : Agent → Finset Good) (i₀ i : Agent) :
    A i ⊆ complete A i₀ i := by
  intro g hg
  exact (mem_complete A i₀ i g).2 (Or.inl hg)

theorem complete_covers (A : Agent → Finset Good) (i₀ : Agent) (g : Good) :
    ∃ i, g ∈ complete A i₀ i := by
  by_cases h : ∃ i, g ∈ A i
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, subset_complete A i₀ i hi⟩
  · exact ⟨i₀, (mem_complete A i₀ i₀ g).2 (Or.inr ⟨rfl, h⟩)⟩

theorem multiplicity_complete (A : Agent → Finset Good) (i₀ : Agent) (g : Good) :
    multiplicity (complete A i₀) g = max 1 (multiplicity A g) := by
  classical
  by_cases h : ∃ i, g ∈ A i
  · have heq : multiplicity (complete A i₀) g = multiplicity A g := by
      simp only [multiplicity]
      congr 1
      ext i
      simp [mem_complete, h]
    have hpos : 0 < multiplicity A g := by
      obtain ⟨i, hi⟩ := h
      exact card_pos.mpr ⟨i, by simp [hi]⟩
    rw [heq, max_eq_right (by omega)]
  · have hempty : multiplicity A g = 0 := by
      simp only [multiplicity, card_eq_zero]
      ext i
      simp only [mem_filter, mem_univ, true_and, not_mem_empty, iff_false]
      exact fun hi => h ⟨i, hi⟩
    have hone : multiplicity (complete A i₀) g = 1 := by
      have heq : (univ.filter fun i => g ∈ complete A i₀ i) = {i₀} := by
        ext i
        have hi : g ∉ A i := fun hi => h ⟨i, hi⟩
        simp [mem_complete, hi, h]
      simp [multiplicity, heq]
    simp [hempty, hone]

theorem extraCopies_complete (A : Agent → Finset Good) (i₀ : Agent) (g : Good) :
    extraCopies (complete A i₀) g = extraCopies A g := by
  simp only [extraCopies, multiplicity_complete]
  omega

theorem totalCopies_complete (A : Agent → Finset Good) (i₀ : Agent) :
    totalCopies (complete A i₀) = totalCopies A := by
  simp only [totalCopies, extraCopies_complete]

theorem multiplicity_complete_le (A : Agent → Finset Good) (i₀ : Agent) (q : ℕ)
    (hq : 1 ≤ q) (hcap : ∀ g, multiplicity A g ≤ q) :
    ∀ g, multiplicity (complete A i₀) g ≤ q := by
  intro g
  rw [multiplicity_complete]
  exact max_le hq (hcap g)

theorem extraCopies_complete_le (A : Agent → Finset Good) (i₀ : Agent) (k : ℕ)
    (hcap : ∀ g, extraCopies A g ≤ k) :
    ∀ g, extraCopies (complete A i₀) g ≤ k := by
  intro g
  simpa only [extraCopies_complete] using hcap g

def utility (v : Agent → Good → ℝ) (A : Agent → Finset Good) (i : Agent) : ℝ :=
  ∑ g ∈ A i, v i g

theorem utility_complete_ge (v : Agent → Good → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (A : Agent → Finset Good) (i₀ i : Agent) :
    utility v A i ≤ utility v (complete A i₀) i := by
  apply sum_le_sum_of_subset_of_nonneg (subset_complete A i₀ i)
  intro g _ _
  exact hv i g

theorem utility_transfer_from_completion (v : Agent → Good → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (A : Agent → Finset Good) (i₀ : Agent)
    (w : Agent → ℝ) (hw : ∀ i, utility v (complete A i₀) i ≤ w i) :
    ∀ i, utility v A i ≤ w i := by
  intro i
  exact (utility_complete_ge v hv A i₀ i).trans (hw i)

/-! A rankwise assignment gives the claimed additive utility guarantee.
The finite set `T` may be the slots belonging to any one agent. -/

theorem rankwise_utility_transfer {Slot : Type*} {m : ℕ}
    (T : Finset Slot) (pos : Slot → Fin m) (f : Slot → Good)
    (rank : Good ≃ Fin m) (v : Good → ℝ)
    (hv : Antitone (fun j => v (rank.symm j)))
    (hinj : Set.InjOn f (↑T : Set Slot))
    (hbound : ∀ s ∈ T, rank (f s) ≤ pos s) :
    (∑ s ∈ T, v (rank.symm (pos s))) ≤ ∑ g ∈ T.image f, v g := by
  rw [Finset.sum_image hinj]
  apply Finset.sum_le_sum
  intro s hs
  simpa only [Equiv.symm_apply_apply] using hv (hbound s hs)


end OrderedReductionCompletion


/-! ## Formal module: Allocation -/

/-!
# Allocation-level consequences of the ordered slot transfer theorem

Slots are the incidences (agent, virtual rank) in an allocation.  These lemmas
translate a rankwise slot assignment back into genuine sets of goods and
verify both utility guarantees and copy budgets.
-/

namespace OrderedReductionAllocation

open Finset Function OrderedReduction OrderedReductionCompletion

variable {Agent Good Slot : Type*}
variable [Fintype Agent] [DecidableEq Agent]
variable [Fintype Good] [DecidableEq Good]

abbrev AllocSlot {m : ℕ} (A : Agent → Finset (Fin m)) :=
  {p : Agent × Fin m // p.2 ∈ A p.1}

def allocOwner {m : ℕ} (A : Agent → Finset (Fin m)) (s : AllocSlot A) : Agent :=
  s.val.1

def allocPos {m : ℕ} (A : Agent → Finset (Fin m)) (s : AllocSlot A) : Fin m :=
  s.val.2

theorem allocSlot_separated {m : ℕ} (A : Agent → Finset (Fin m)) :
    Injective (fun s : AllocSlot A => (allocOwner A s, allocPos A s)) := by
  intro s t h
  exact Subtype.ext h

theorem allocSlot_multiplicity {m : ℕ} (A : Agent → Finset (Fin m)) (j : Fin m) :
    slotMultiplicity (allocPos A) j = multiplicity A j := by
  classical
  unfold slotMultiplicity OrderedReductionCompletion.multiplicity
  refine Finset.card_bij (fun s _ => s.val.1) ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_univ, true_and, allocPos] at hs ⊢
    simpa only [hs] using s.property
  · intro s hs t ht hst
    simp only [mem_filter, mem_univ, true_and, allocPos] at hs ht
    exact Subtype.ext (Prod.ext hst (hs.trans ht.symm))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    exact ⟨⟨(i, j), hi⟩, by simp [allocPos], rfl⟩

theorem sum_allocSlot_values {m : ℕ} (A : Agent → Finset (Fin m))
    (i : Agent) (w : Fin m → ℝ) :
    (∑ s ∈ univ.filter (fun s : AllocSlot A => allocOwner A s = i),
      w (allocPos A s)) = ∑ j ∈ A i, w j := by
  classical
  refine Finset.sum_bij (fun s _ => s.val.2) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_univ, true_and, allocOwner] at hs
    simpa only [hs] using s.property
  · intro s hs t ht hst
    simp only [mem_filter, mem_univ, true_and, allocOwner] at hs ht
    exact Subtype.ext (Prod.ext (hs.trans ht.symm) hst)
  · intro j hj
    exact ⟨⟨(i, j), hj⟩, by simp [allocOwner], rfl⟩
  · intro s hs
    rfl

def imageAllocation [Fintype Slot] (owner : Slot → Agent) (f : Slot → Good)
    (i : Agent) : Finset Good :=
  (univ.filter fun s => owner s = i).image f

theorem imageAllocation_multiplicity [Fintype Slot]
    (owner : Slot → Agent) (f : Slot → Good)
    (hinj : Injective (fun s => (owner s, f s))) (g : Good) :
    multiplicity (imageAllocation owner f) g =
      (univ.filter fun s => f s = g).card := by
  classical
  unfold OrderedReductionCompletion.multiplicity
  symm
  refine Finset.card_bij (fun s _ => owner s) ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact mem_image.mpr ⟨s, by simp, hs⟩
  · intro s hs t ht hst
    simp only [mem_filter, mem_univ, true_and] at hs ht
    exact hinj (Prod.ext hst (hs.trans ht.symm))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and, imageAllocation, mem_image] at hi
    obtain ⟨s, hs, hf⟩ := hi
    exact ⟨s, by simp [hf], by simpa using hs⟩

theorem imageAllocation_multiplicity_sum [Fintype Slot]
    (owner : Slot → Agent) (f : Slot → Good)
    (hinj : Injective (fun s => (owner s, f s))) :
    (∑ g, multiplicity (imageAllocation owner f) g) = Fintype.card Slot := by
  classical
  simp_rw [imageAllocation_multiplicity owner f hinj]
  simpa using (Finset.sum_card_fiberwise_eq_card_filter univ univ f)

theorem totalCopies_eq_sum_sub (A : Agent → Finset Good)
    (hcover : ∀ g, 1 ≤ multiplicity A g) :
    totalCopies A = (∑ g, multiplicity A g) - Fintype.card Good := by
  unfold totalCopies extraCopies
  calc
    (∑ g, (multiplicity A g - 1)) =
        (∑ g, multiplicity A g) - ∑ _g : Good, 1 :=
      Finset.sum_tsub_distrib univ (fun g _ => hcover g)
    _ = (∑ g, multiplicity A g) - Fintype.card Good := by simp

theorem allocation_from_slot_assignment
    (A : Agent → Finset (Fin (Fintype.card Good)))
    (rank : Agent → Good ≃ Fin (Fintype.card Good))
    (v : Agent → Good → ℝ)
    (hv : ∀ i, Antitone (fun j => v i ((rank i).symm j)))
    (q : ℕ) (hcover : ∀ j, 1 ≤ multiplicity A j)
    (a : AllocSlot A → Agent × Good) (hinj : Injective a)
    (hvalid : ∀ s, (a s).1 = allocOwner A s ∧
      rank (allocOwner A s) (a s).2 ≤ allocPos A s)
    (hcounts : ∀ g, 1 ≤ (univ.filter (fun s => (a s).2 = g)).card ∧
      (univ.filter (fun s => (a s).2 = g)).card ≤ q) :
    ∃ B : Agent → Finset Good,
      (∀ g, 1 ≤ multiplicity B g ∧ multiplicity B g ≤ q) ∧
      totalCopies B = totalCopies A ∧
      ∀ i, utility (fun i j => v i ((rank i).symm j)) A i ≤ utility v B i := by
  classical
  let f : AllocSlot A → Good := fun s => (a s).2
  let B : Agent → Finset Good := imageAllocation (allocOwner A) f
  have hpair : Injective (fun s => (allocOwner A s, f s)) := by
    intro s t h
    apply hinj
    apply Prod.ext
    · rw [(hvalid s).1, (hvalid t).1]
      exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).2
  have hBcounts : ∀ g, 1 ≤ multiplicity B g ∧ multiplicity B g ≤ q := by
    intro g
    simpa only [B, imageAllocation_multiplicity _ _ hpair] using hcounts g
  refine ⟨B, hBcounts, ?_, ?_⟩
  · rw [totalCopies_eq_sum_sub B (fun g => (hBcounts g).1),
      totalCopies_eq_sum_sub A hcover]
    have hsumA : (∑ j, multiplicity A j) = Fintype.card (AllocSlot A) := by
      simpa only [allocSlot_multiplicity] using slotMultiplicity_sum (allocPos A)
    rw [hsumA]
    simpa only [B, Fintype.card_fin] using
      congrArg (fun z => z - Fintype.card Good)
        (imageAllocation_multiplicity_sum (allocOwner A) f hpair)
  · intro i
    unfold utility
    rw [← sum_allocSlot_values A i (fun j => v i ((rank i).symm j))]
    apply rankwise_utility_transfer
      (univ.filter (fun s : AllocSlot A => allocOwner A s = i))
      (allocPos A) f (rank i) (v i) (hv i)
    · intro s hs t ht hst
      have hs' := (Finset.mem_filter.mp hs).2
      have ht' := (Finset.mem_filter.mp ht).2
      exact hpair (Prod.ext (hs'.trans ht'.symm) hst)
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      simpa only [hs] using (hvalid s).2


end OrderedReductionAllocation


/-! ## Formal module: Main -/

/-!
# General ordered-instance reduction with copies

The final theorem permits arbitrary ordered allocations, including unused
goods, and preserves both copy budgets from Definition 2.5 of
arXiv:2502.09377.  Every output bundle is a finite set, so an agent never
receives two copies of the same good.
-/

namespace OrderedReductionAllocation

open Finset Function OrderedReduction OrderedReductionCompletion

variable {Agent Good : Type*}
variable [Fintype Agent] [DecidableEq Agent]
variable [Fintype Good] [DecidableEq Good]

theorem complete_allocation_transfer
    (A : Agent → Finset (Fin (Fintype.card Good)))
    (rank : Agent → Good ≃ Fin (Fintype.card Good))
    (v : Agent → Good → ℝ)
    (hv : ∀ i, Antitone (fun j => v i ((rank i).symm j)))
    (q : ℕ) (hq : 1 ≤ q)
    (hcover : ∀ j, 1 ≤ multiplicity A j)
    (hcap : ∀ j, multiplicity A j ≤ q) :
    ∃ B : Agent → Finset Good,
      (∀ g, 1 ≤ multiplicity B g ∧ multiplicity B g ≤ q) ∧
      totalCopies B = totalCopies A ∧
      ∀ i, utility (fun i j => v i ((rank i).symm j)) A i ≤ utility v B i := by
  classical
  obtain ⟨a, hinj, hvalid, hcounts⟩ :=
    ordered_slots_transfer q hq (allocOwner A) (allocPos A) rank
      (allocSlot_separated A)
      (fun j => by simpa only [allocSlot_multiplicity] using hcover j)
      (fun j => by simpa only [allocSlot_multiplicity] using hcap j)
  exact allocation_from_slot_assignment A rank v hv q hcover a hinj hvalid hcounts

/-- The reduction preserves the actual total number of extra copies exactly.
Here `k` counts extra copies per good, so the maximum multiplicity is `k+1`.
Unallocated virtual goods are permitted in the input. -/
theorem ordered_allocation_transfer_exact [Nonempty Agent]
    (A : Agent → Finset (Fin (Fintype.card Good)))
    (rank : Agent → Good ≃ Fin (Fintype.card Good))
    (v : Agent → Good → ℝ)
    (hnonneg : ∀ i g, 0 ≤ v i g)
    (hordered : ∀ i, Antitone (fun j => v i ((rank i).symm j)))
    (k : ℕ)
    (hpergood : ∀ j, extraCopies A j ≤ k) :
    ∃ B : Agent → Finset Good,
      (∀ i, utility (fun i j => v i ((rank i).symm j)) A i ≤ utility v B i) ∧
      totalCopies B = totalCopies A ∧
      (∀ g, extraCopies B g ≤ k) ∧
      ∀ g, 1 ≤ multiplicity B g := by
  classical
  let i₀ : Agent := Classical.arbitrary Agent
  let C : Agent → Finset (Fin (Fintype.card Good)) := complete A i₀
  have hCcover : ∀ j, 1 ≤ multiplicity C j := by
    intro j
    change 1 ≤ multiplicity (complete A i₀) j
    rw [multiplicity_complete]
    exact le_max_left _ _
  have hCcap : ∀ j, multiplicity C j ≤ k + 1 := by
    intro j
    have he : extraCopies C j ≤ k := by
      simpa only [C, extraCopies_complete] using hpergood j
    have hl := hCcover j
    unfold extraCopies at he
    omega
  obtain ⟨B, hBcounts, hcopies, hutils⟩ :=
    complete_allocation_transfer C rank v hordered (k + 1) (by omega) hCcover hCcap
  refine ⟨B, ?_, ?_, ?_, fun g => (hBcounts g).1⟩
  · intro i
    have hAC := utility_complete_ge
      (fun i j => v i ((rank i).symm j))
      (fun i j => hnonneg i ((rank i).symm j)) A i₀ i
    exact hAC.trans (hutils i)
  · exact hcopies.trans (totalCopies_complete A i₀)
  · intro g
    have hg := (hBcounts g).2
    unfold extraCopies
    omega

/-- Every ordered (t,k)-allocation transfers to the original additive
instance without increasing either copy budget or reducing anyone's value.
No restriction on which ranks are copied or on their recipients is imposed. -/
theorem ordered_allocation_transfer [Nonempty Agent]
    (A : Agent → Finset (Fin (Fintype.card Good)))
    (rank : Agent → Good ≃ Fin (Fintype.card Good))
    (v : Agent → Good → ℝ)
    (hnonneg : ∀ i g, 0 ≤ v i g)
    (hordered : ∀ i, Antitone (fun j => v i ((rank i).symm j)))
    (t k : ℕ)
    (htotal : totalCopies A ≤ t)
    (hpergood : ∀ j, extraCopies A j ≤ k) :
    ∃ B : Agent → Finset Good,
      (∀ i, utility (fun i j => v i ((rank i).symm j)) A i ≤ utility v B i) ∧
      totalCopies B ≤ t ∧
      (∀ g, extraCopies B g ≤ k) ∧
      ∀ g, 1 ≤ multiplicity B g := by
  obtain ⟨B, hutils, hcopies, hcap, hcover⟩ :=
    ordered_allocation_transfer_exact A rank v hnonneg hordered k hpergood
  exact ⟨B, hutils, hcopies ▸ htotal, hcap, hcover⟩

/-- Consequently every vector of agent-specific utility thresholds attained
in the ordered instance can be attained with the same copy budgets. -/
theorem ordered_threshold_transfer [Nonempty Agent]
    (A : Agent → Finset (Fin (Fintype.card Good)))
    (rank : Agent → Good ≃ Fin (Fintype.card Good))
    (v : Agent → Good → ℝ)
    (hnonneg : ∀ i g, 0 ≤ v i g)
    (hordered : ∀ i, Antitone (fun j => v i ((rank i).symm j)))
    (t k : ℕ) (threshold : Agent → ℝ)
    (htotal : totalCopies A ≤ t)
    (hpergood : ∀ j, extraCopies A j ≤ k)
    (hthreshold : ∀ i, threshold i ≤
      utility (fun i j => v i ((rank i).symm j)) A i) :
    ∃ B : Agent → Finset Good,
      (∀ i, threshold i ≤ utility v B i) ∧
      totalCopies B ≤ t ∧ (∀ g, extraCopies B g ≤ k) := by
  obtain ⟨B, hutils, htotalB, hpergoodB, _⟩ :=
    ordered_allocation_transfer A rank v hnonneg hordered t k htotal hpergood
  exact ⟨B, fun i => (hthreshold i).trans (hutils i), htotalB, hpergoodB⟩


end OrderedReductionAllocation


#print axioms OrderedReductionAllocation.ordered_allocation_transfer_exact
#print axioms OrderedReductionAllocation.ordered_allocation_transfer
#print axioms OrderedReductionAllocation.ordered_threshold_transfer
