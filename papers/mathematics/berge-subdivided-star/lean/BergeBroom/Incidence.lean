import BergeBroom.Definitions
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # Incidence graph cardinality, derived from the actual hyperedges -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge

open scoped BigOperators

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

def vertexPart (E : Finset (Finset V)) : Finset (V ⊕ {e // e ∈ E}) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

def edgePart (E : Finset (Finset V)) : Finset (V ⊕ {e // e ∈ E}) :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

theorem incidence_bipartite (E : Finset (Finset V)) :
    (incidenceGraph E).IsBipartiteWith (vertexPart E) (edgePart E) := by
  constructor
  · rw [Finset.disjoint_coe]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hx
    simp [edgePart] at hy
  · intro x y h
    cases x <;> cases y <;> simp_all [incidenceGraph, vertexPart, edgePart]

theorem incidence_neighborFinset_edge (E : Finset (Finset V))
    (e : {e // e ∈ E}) :
    (incidenceGraph E).neighborFinset (.inr e) =
      e.val.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  ext x
  cases x <;> simp [SimpleGraph.mem_neighborFinset]

@[simp] theorem incidence_degree_edge (E : Finset (Finset V))
    (e : {e // e ∈ E}) :
    (incidenceGraph E).degree (.inr e) = e.val.card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, incidence_neighborFinset_edge]
  simp

def incidenceNeighborEquiv (E : Finset (Finset V)) (v : V) :
    (incidenceGraph E).neighborSet (.inl v) ≃ {e // e ∈ incidentEdges E v} where
  toFun := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | inl w => exact False.elim hx
    | inr e => exact ⟨e.val, mem_incidentEdges.mpr ⟨e.property, hx⟩⟩
  invFun := fun e =>
    ⟨.inr ⟨e.val, (mem_incidentEdges.mp e.property).1⟩,
      (mem_incidentEdges.mp e.property).2⟩
  left_inv := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | inl w => exact False.elim hx
    | inr e => rfl
  right_inv := by intro e; rfl

@[simp] theorem incidence_degree_vertex (E : Finset (Finset V)) (v : V) :
    (incidenceGraph E).degree (.inl v) = degree E v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (incidenceNeighborEquiv E v)).trans
    (Fintype.card_coe (incidentEdges E v))

theorem incidence_edge_card {r : ℕ} (H : UniformHypergraph V r) :
    (incidenceGraph H.edges).edgeFinset.card = r * H.edges.card := by
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
    (incidence_bipartite H.edges)
  have hd (e : {e // e ∈ H.edges}) :
      (incidenceGraph H.edges).degree (.inr e) = r :=
    (incidence_degree_edge H.edges e).trans (H.uniform e.val e.property)
  simpa [edgePart, hd, Nat.mul_comm] using h.symm

theorem sum_degrees {r : ℕ} (H : UniformHypergraph V r) :
    ∑ v : V, degree H.edges v = r * H.edges.card := by
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (incidence_bipartite H.edges)
  simpa [vertexPart, incidence_edge_card H] using h

theorem incidence_edge_natCard {r : ℕ} (H : UniformHypergraph V r) :
    Nat.card (incidenceGraph H.edges).edgeSet = r * H.edges.card := by
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  exact incidence_edge_card H

theorem incidence_vertex_natCard (E : Finset (Finset V)) :
    Nat.card (V ⊕ {e // e ∈ E}) = Fintype.card V + E.card := by
  simp [Nat.card_eq_fintype_card, Fintype.card_sum]

theorem connected_vertex_bound {r : ℕ} (hr : 1 ≤ r) (H : UniformHypergraph V r)
    (hc : (incidenceGraph H.edges).Connected) :
    Fintype.card V ≤ (r - 1) * H.edges.card + 1 := by
  have h := hc.card_vert_le_card_edgeSet_add_one
  rw [incidence_vertex_natCard, incidence_edge_natCard H] at h
  have hm : r * H.edges.card = (r - 1) * H.edges.card + H.edges.card := by
    calc
      r * H.edges.card = ((r - 1) + 1) * H.edges.card := by
        rw [Nat.sub_add_cancel hr]
      _ = (r - 1) * H.edges.card + H.edges.card := by rw [add_mul, one_mul]
  omega

theorem incidence_isTree_iff {r : ℕ} (hr : 1 ≤ r) (H : UniformHypergraph V r) :
    (incidenceGraph H.edges).IsTree ↔
      (incidenceGraph H.edges).Connected ∧
        Fintype.card V = (r - 1) * H.edges.card + 1 := by
  rw [SimpleGraph.isTree_iff_connected_and_card,
    incidence_edge_natCard H, incidence_vertex_natCard]
  have hm : r * H.edges.card = (r - 1) * H.edges.card + H.edges.card := by
    calc
      r * H.edges.card = ((r - 1) + 1) * H.edges.card := by
        rw [Nat.sub_add_cancel hr]
      _ = (r - 1) * H.edges.card + H.edges.card := by rw [add_mul, one_mul]
  constructor <;> rintro ⟨hc, he⟩ <;> exact ⟨hc, by omega⟩

theorem connected_not_tree_vertex_bound {r : ℕ} (hr : 1 ≤ r)
    (H : UniformHypergraph V r) (hc : (incidenceGraph H.edges).Connected)
    (ht : ¬ (incidenceGraph H.edges).IsTree) :
    Fintype.card V ≤ (r - 1) * H.edges.card := by
  have h := connected_vertex_bound hr H hc
  have hn : Fintype.card V ≠ (r - 1) * H.edges.card + 1 := by
    intro he
    exact ht ((incidence_isTree_iff hr H).mpr ⟨hc, he⟩)
  omega

theorem BroomCopy.center_reachable_stem {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) :
    (incidenceGraph E).Reachable (.inl (C.core 0)) (.inl (C.core (stemVertex a))) := by
  have hl : (incidenceGraph E).Adj (.inl (C.core 0)) (.inr (C.edge 0)) := by
    simpa [incidenceGraph, broomLeft] using C.left_mem 0
  have hr : (incidenceGraph E).Adj (.inr (C.edge 0))
      (.inl (C.core (stemVertex a))) := by
    simpa [incidenceGraph, broomRight, stemVertex] using C.right_mem 0
  exact hl.reachable.trans hr.reachable

theorem BroomCopy.center_reachable_edge {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) (i : Fin (a + 1)) :
    (incidenceGraph E).Reachable (.inl (C.core 0)) (.inr (C.edge i)) := by
  have hl : (incidenceGraph E).Adj (.inl (C.core (broomLeft a i)))
      (.inr (C.edge i)) := C.left_mem i
  by_cases hi : i.val = 1
  · have hr : (incidenceGraph E).Reachable (.inl (C.core 0))
        (.inl (C.core (broomLeft a i))) := by
      simpa [broomLeft, hi, stemVertex] using C.center_reachable_stem
    exact hr.trans hl.reachable
  · simpa [broomLeft, hi] using hl.reachable

theorem BroomCopy.center_reachable_core {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) (j : Fin (a + 2)) :
    (incidenceGraph E).Reachable (.inl (C.core 0)) (.inl (C.core j)) := by
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    exact SimpleGraph.Reachable.refl _
  · let i : Fin (a + 1) := ⟨j.val - 1, by omega⟩
    have he : broomRight a i = j := by
      apply Fin.ext
      dsimp [broomRight, i]
      omega
    have hr : (incidenceGraph E).Adj (.inr (C.edge i)) (.inl (C.core j)) := by
      simpa [he] using C.right_mem i
    exact (C.center_reachable_edge i).trans hr.reachable

theorem BroomCopy.edge_component_eq {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) (i : Fin (a + 1)) :
    (incidenceGraph E).connectedComponentMk (.inr (C.edge i)) =
      (incidenceGraph E).connectedComponentMk (.inl (C.core 0)) :=
  SimpleGraph.ConnectedComponent.sound (C.center_reachable_edge i).symm

theorem BroomCopy.core_component_eq {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) (j : Fin (a + 2)) :
    (incidenceGraph E).connectedComponentMk (.inl (C.core j)) =
      (incidenceGraph E).connectedComponentMk (.inl (C.core 0)) :=
  SimpleGraph.ConnectedComponent.sound (C.center_reachable_core j).symm

end Berge
