import BergeBroom.Incidence
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge
open scoped BigOperators
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

def degreeOneVertices (E : Finset (Finset V)) : Finset V :=
  Finset.univ.filter (fun v => degree E v=1)

@[simp] theorem mem_degreeOneVertices {E : Finset (Finset V)} {v : V} :
    v∈degreeOneVertices E ↔ degree E v=1 := by simp [degreeOneVertices]

theorem connected_degree_pos {E : Finset (Finset V)}
    (hc : (incidenceGraph E).Connected) (hE : E.Nonempty) (v : V) :
    0<degree E v := by
  obtain ⟨e,he⟩ := hE
  obtain ⟨p⟩ := hc (.inl v) (.inr ⟨e,he⟩)
  have hn : ¬p.Nil := by
    intro h
    exact Sum.inl_ne_inr h.eq
  rw [←incidence_degree_vertex,SimpleGraph.degree_pos_iff_exists_adj]
  exact ⟨p.snd,p.adj_snd hn⟩

/-- An edge consisting entirely of degree-one vertices is its whole connected
component. This is proved by propagating a closed predicate along incidence walks. -/
theorem connected_all_leaf_edge_card_le_one {E : Finset (Finset V)}
    (hc : (incidenceGraph E).Connected) {e : Finset V} (he : e∈E)
    (hleaf : ∀ v∈e, degree E v=1) : E.card≤1 := by
  let P : (V ⊕ {f // f∈E}) → Prop := fun w =>
    match w with
    | .inl v => v∈e
    | .inr f => f.val=e
  have hclosed (x y : V ⊕ {f // f∈E}) (hxy : (incidenceGraph E).Adj x y)
      (hx : P x) : P y := by
    rcases x with v | f <;> rcases y with w | g
    · exact False.elim hxy
    · change g.val=e
      change v∈e at hx
      have hd : (incidentEdges E v).card≤1 := by
        change degree E v≤1
        rw [hleaf v hx]
      exact Finset.card_le_one.mp hd g.val
        (mem_incidentEdges.mpr ⟨g.property,hxy⟩) e
        (mem_incidentEdges.mpr ⟨he,hx⟩)
    · change w∈e
      change f.val=e at hx
      rw [←hx]
      exact hxy
    · exact False.elim hxy
  have hprop {x y : V ⊕ {f // f∈E}} (p : (incidenceGraph E).Walk x y) :
      P x → P y := by
    induction p with
    | nil => exact id
    | cons hxy p ih => exact fun hx => ih (hclosed _ _ hxy hx)
  have hall (f : Finset V) (hf : f∈E) : f=e := by
    obtain ⟨p⟩ := hc (.inr ⟨e,he⟩) (.inr ⟨f,hf⟩)
    exact hprop p rfl
  apply Finset.card_le_one.mpr
  intro f hf g hg
  exact (hall f hf).trans (hall g hg).symm

theorem leaf_sum_bound {r : ℕ} (H : UniformHypergraph V r)
    (hp : ∀ v, 0<degree H.edges v) :
    2*Fintype.card V ≤ r*H.edges.card+(degreeOneVertices H.edges).card := by
  have hpoint (v : V) : 2≤degree H.edges v+(if degree H.edges v=1 then 1 else 0) := by
    split_ifs with h
    · omega
    · have hh := hp v
      omega
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => hpoint v)
  simpa [Finset.sum_add_distrib,Finset.sum_ite,degreeOneVertices,
    sum_degrees H,Nat.mul_comm] using hsum

theorem incidence_tree_leaf_count {r : ℕ} (hr : 2≤r) (H : UniformHypergraph V r)
    (ht : (incidenceGraph H.edges).IsTree) (hm : 1≤H.edges.card) :
    (r-2)*H.edges.card+2 ≤ (degreeOneVertices H.edges).card := by
  have hconn := (incidence_isTree_iff (by omega) H).mp ht
  have hn := hconn.2
  have hnon : H.edges.Nonempty := Finset.card_pos.mp (by omega)
  have hb := leaf_sum_bound H (connected_degree_pos hconn.1 hnon)
  have h1 : r*H.edges.card=(r-2)*H.edges.card+2*H.edges.card := by
    calc
      r*H.edges.card=((r-2)+2)*H.edges.card := by rw [Nat.sub_add_cancel hr]
      _ = _ := by ring
  have h2 : (r-1)*H.edges.card=(r-2)*H.edges.card+H.edges.card := by
    have he : r-1=(r-2)+1 := by omega
    rw [he]
    ring
  rw [hn,h1,h2] at hb
  omega

theorem incidence_tree_many_leaves {r : ℕ} (hr : 3≤r) (H : UniformHypergraph V r)
    (ht : (incidenceGraph H.edges).IsTree) (hm : 2≤H.edges.card) :
    r ≤ (degreeOneVertices H.edges).card := by
  have h := incidence_tree_leaf_count (by omega) H ht (by omega)
  have hmul := Nat.mul_le_mul_left (r-2) hm
  have h2 : (r-2)*2+2≥r := by omega
  omega

theorem saturated_tree_has_high_degree {a r : ℕ} (ha : 3≤a) (hr : 3≤r)
    (H : UniformHypergraph V r) (hSat : Saturated a H)
    (ht : (incidenceGraph H.edges).IsTree) (hm : 2≤H.edges.card) :
    ∃ v, a≤degree H.edges v := by
  classical
  by_contra hn
  have hlow (v : V) : degree H.edges v<a := by
    by_contra hv
    exact hn ⟨v,by omega⟩
  obtain ⟨T,hTsub,hTcard⟩ := Finset.exists_subset_card_eq
    (incidence_tree_many_leaves hr H ht hm)
  have hmissing : T∉H.edges := by
    intro hmem
    have hle := connected_all_leaf_edge_card_le_one
      ((incidence_isTree_iff (by omega) H).mp ht).1 hmem
      (fun v hv => mem_degreeOneVertices.mp (hTsub hv))
    omega
  have hfree : BroomFree a (insert T H.edges) := by
    apply free_of_degrees_lt
    intro v
    by_cases hv : v∈T
    · have hd : degree H.edges v=1 := mem_degreeOneVertices.mp (hTsub hv)
      have hi := degree_insert_le H.edges T v
      omega
    · rw [degree_insert_of_not_mem H.edges T v hv]
      exact hlow v
  exact hfree (hSat.2 T hTcard hmissing)

end Berge
