import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/-!
# Simple uniform hypergraphs and actual Berge broom copies

Edges are finite sets of vertices, and the hypergraph is a finite set of edges.
The broom has core vertices `0 = center`, `1 = stem`, `2 = terminal`, and
`3, ..., a+1` for its ordinary leaves. Its edges are indexed by `Fin (a+1)`:
edge 0 joins 0 to 1, edge 1 joins 1 to 2, and edge i >= 2 joins 0 to i+1.
Both the core map and the map from broom edges to hyperedges are injective.
No restriction forbids additional core vertices inside an assigned hyperedge.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge

universe u

variable {V : Type u} [DecidableEq V]

/-- A simple finite `r`-uniform hypergraph, retaining the entire ambient vertex type. -/
structure UniformHypergraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- Left endpoint of a broom edge. -/
def broomLeft (a : ℕ) (i : Fin (a + 1)) : Fin (a + 2) :=
  ⟨if i.val = 1 then 1 else 0, by split_ifs <;> omega⟩

/-- Right endpoint of a broom edge. -/
def broomRight (a : ℕ) (i : Fin (a + 1)) : Fin (a + 2) :=
  ⟨i.val + 1, by omega⟩

theorem broom_endpoints_ne (a : ℕ) (i : Fin (a + 1)) :
    broomLeft a i ≠ broomRight a i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [broomLeft, broomRight] at hv
  split_ifs at hv
  omega

/-- An actual Berge copy, including both required injections. -/
structure BroomCopy (a : ℕ) (E : Finset (Finset V)) where
  core : Fin (a + 2) ↪ V
  edge : Fin (a + 1) ↪ {e // e ∈ E}
  left_mem : ∀ i, core (broomLeft a i) ∈ (edge i).val
  right_mem : ∀ i, core (broomRight a i) ∈ (edge i).val

def ContainsBroom (a : ℕ) (E : Finset (Finset V)) : Prop :=
  Nonempty (BroomCopy a E)

def BroomFree (a : ℕ) (E : Finset (Finset V)) : Prop :=
  ¬ ContainsBroom a E

/-- Saturation tests every missing `r`-set, including those containing isolates. -/
def Saturated {r : ℕ} (a : ℕ) (H : UniformHypergraph V r) : Prop :=
  BroomFree a H.edges ∧
    ∀ e : Finset V, e.card = r → e ∉ H.edges → ContainsBroom a (insert e H.edges)

def incidentEdges (E : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  E.filter (fun e => v ∈ e)

def degree (E : Finset (Finset V)) (v : V) : ℕ :=
  (incidentEdges E v).card

def support (E : Finset (Finset V)) : Finset V :=
  E.biUnion id

@[simp] theorem mem_incidentEdges {E : Finset (Finset V)} {v : V} {e : Finset V} :
    e ∈ incidentEdges E v ↔ e ∈ E ∧ v ∈ e := by
  simp [incidentEdges]

theorem degree_le_edge_card (E : Finset (Finset V)) (v : V) :
    degree E v ≤ E.card := Finset.card_filter_le _ _

theorem BroomCopy.edge_card_le {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) : a + 1 ≤ E.card := by
  simpa using Fintype.card_le_of_injective C.edge C.edge.injective

theorem BroomCopy.vertex_card_le [Fintype V] {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) : a + 2 ≤ Fintype.card V := by
  simpa using Fintype.card_le_of_injective C.core C.core.injective

theorem free_of_edge_card_le {a : ℕ} {E : Finset (Finset V)}
    (h : E.card ≤ a) : BroomFree a E := by
  rintro ⟨C⟩
  have := C.edge_card_le
  omega

theorem free_of_vertex_card_le [Fintype V] {a : ℕ} {E : Finset (Finset V)}
    (h : Fintype.card V ≤ a + 1) : BroomFree a E := by
  rintro ⟨C⟩
  have := C.vertex_card_le
  omega

def BroomCopy.mono {a : ℕ} {E F : Finset (Finset V)}
    (C : BroomCopy a E) (hEF : E ⊆ F) : BroomCopy a F where
  core := C.core
  edge :=
    { toFun := fun i => ⟨(C.edge i).val, hEF (C.edge i).property⟩
      inj' := by
        intro i j h
        apply C.edge.injective
        exact Subtype.ext (congrArg (fun z : {e // e ∈ F} => z.val) h) }
  left_mem := C.left_mem
  right_mem := C.right_mem

theorem contains_mono {a : ℕ} {E F : Finset (Finset V)}
    (hEF : E ⊆ F) (h : ContainsBroom a E) : ContainsBroom a F := by
  obtain ⟨C⟩ := h
  exact ⟨C.mono hEF⟩

theorem free_of_subset {a : ℕ} {E F : Finset (Finset V)}
    (hEF : E ⊆ F) (hF : BroomFree a F) : BroomFree a E :=
  fun hE => hF (contains_mono hEF hE)

def BroomCopy.restrictEdges {a : ℕ} {E F : Finset (Finset V)}
    (C : BroomCopy a E) (h : ∀ i, (C.edge i).val ∈ F) : BroomCopy a F where
  core := C.core
  edge :=
    { toFun := fun i => ⟨(C.edge i).val, h i⟩
      inj' := by
        intro i j hij
        apply C.edge.injective
        exact Subtype.ext (congrArg (fun z : {e // e ∈ F} => z.val) hij) }
  left_mem := C.left_mem
  right_mem := C.right_mem

theorem BroomCopy.uses_inserted_edge {a : ℕ} {E : Finset (Finset V)} {e : Finset V}
    (C : BroomCopy a (insert e E)) (hfree : BroomFree a E) :
    ∃ i, (C.edge i).val = e := by
  by_contra hn
  push Not at hn
  apply hfree
  exact ⟨C.restrictEdges (fun i =>
    (Finset.mem_insert.mp (C.edge i).property).resolve_left (hn i))⟩

def BroomCopy.mapVerticesInto {W : Type*} [DecidableEq W]
    {a : ℕ} {E : Finset (Finset V)} {F : Finset (Finset W)}
    (C : BroomCopy a E) (f : V ↪ W) (h : ∀ e ∈ E, e.map f ∈ F) : BroomCopy a F where
  core := C.core.trans f
  edge :=
    { toFun := fun i => ⟨(C.edge i).val.map f, h _ (C.edge i).property⟩
      inj' := by
        intro i j hij
        apply C.edge.injective
        apply Subtype.ext
        apply Finset.map_injective f
        exact congrArg (fun z : {e // e ∈ F} => z.val) hij }
  left_mem := fun i => Finset.mem_map.mpr ⟨_, C.left_mem i, rfl⟩
  right_mem := fun i => Finset.mem_map.mpr ⟨_, C.right_mem i, rfl⟩

/-- The `a` broom edges incident to the center; this skips edge index 1. -/
def centerIndex (a : ℕ) (i : Fin a) : Fin (a + 1) :=
  ⟨if i.val = 0 then 0 else i.val + 1, by split_ifs <;> omega⟩

theorem centerIndex_injective (a : ℕ) : Function.Injective (centerIndex a) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [centerIndex] at hv
  split_ifs at hv <;> omega

@[simp] theorem broomLeft_centerIndex (a : ℕ) (i : Fin a) :
    broomLeft a (centerIndex a i) = 0 := by
  apply Fin.ext
  by_cases hi : i.val = 0
  · simp [broomLeft, centerIndex, hi]
  · have h1 : i.val + 1 ≠ 1 := by omega
    simp [broomLeft, centerIndex, hi]

theorem BroomCopy.center_degree_le {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) : a ≤ degree E (C.core 0) := by
  let f : Fin a ↪ {e // e ∈ incidentEdges E (C.core 0)} :=
    { toFun := fun i =>
        ⟨(C.edge (centerIndex a i)).val, by
          apply mem_incidentEdges.mpr
          constructor
          · exact (C.edge (centerIndex a i)).property
          · simpa using C.left_mem (centerIndex a i)⟩
      inj' := by
        intro i j h
        apply centerIndex_injective a
        apply C.edge.injective
        exact Subtype.ext
          (congrArg (fun z : {e // e ∈ incidentEdges E (C.core 0)} => z.val) h) }
  simpa [degree] using Fintype.card_le_of_injective f f.injective

theorem free_of_degrees_lt {a : ℕ} {E : Finset (Finset V)}
    (h : ∀ v, degree E v < a) : BroomFree a E := by
  rintro ⟨C⟩
  exact (Nat.not_le_of_lt (h (C.core 0))) C.center_degree_le

/-- The stem is the vertex of index one, distinct from the center. -/
def stemVertex (a : ℕ) : Fin (a + 2) := ⟨1, by omega⟩

theorem BroomCopy.center_ne_stem {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) : C.core 0 ≠ C.core (stemVertex a) := by
  intro h
  have hv := congrArg Fin.val (C.core.injective h)
  simp [stemVertex] at hv

theorem BroomCopy.stem_degree_le {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) (ha : 1 ≤ a) : 2 ≤ degree E (C.core (stemVertex a)) := by
  let index : Fin 2 → Fin (a + 1) := fun i => ⟨i.val, by omega⟩
  have hmem (i : Fin 2) : C.core (stemVertex a) ∈ (C.edge (index i)).val := by
    fin_cases i
    · simpa [index, broomRight, stemVertex] using C.right_mem (index 0)
    · simpa [index, broomLeft, stemVertex] using C.left_mem (index 1)
  let f : Fin 2 ↪ {e // e ∈ incidentEdges E (C.core (stemVertex a))} :=
    { toFun := fun i =>
        ⟨(C.edge (index i)).val,
          mem_incidentEdges.mpr ⟨(C.edge (index i)).property, hmem i⟩⟩
      inj' := by
        intro i j h
        have hval := congrArg
          (fun z : {e // e ∈ incidentEdges E (C.core (stemVertex a))} => z.val) h
        have hedge := C.edge.injective (Subtype.ext hval)
        exact Fin.ext (congrArg (fun z : Fin (a + 1) => z.val) hedge) }
  simpa [degree] using Fintype.card_le_of_injective f f.injective

/-- In particular, a loose star is free: only its center can have degree above one. -/
theorem free_of_one_high_degree_vertex {a : ℕ} {E : Finset (Finset V)}
    (ha : 2 ≤ a) (c : V) (h : ∀ v, v ≠ c → degree E v ≤ 1) : BroomFree a E := by
  rintro ⟨C⟩
  have hc : C.core 0 = c := by
    by_contra hn
    have := h (C.core 0) hn
    have := C.center_degree_le
    omega
  have hb : C.core (stemVertex a) = c := by
    by_contra hn
    have := h (C.core (stemVertex a)) hn
    have := C.stem_degree_le (by omega)
    omega
  exact C.center_ne_stem (hc.trans hb.symm)

theorem degree_insert_le (E : Finset (Finset V)) (e : Finset V) (v : V) :
    degree (insert e E) v ≤ degree E v + 1 := by
  by_cases h : v ∈ e
  · simpa [degree, incidentEdges, Finset.filter_insert, h] using
      (Finset.card_insert_le e (E.filter (fun f => v ∈ f)))
  · simp [degree, incidentEdges, Finset.filter_insert, h]

theorem degree_insert_of_not_mem (E : Finset (Finset V)) (e : Finset V) (v : V)
    (h : v ∉ e) : degree (insert e E) v = degree E v := by
  simp [degree, incidentEdges, Finset.filter_insert, h]

def UniformHypergraph.addEdge {r : ℕ} (H : UniformHypergraph V r)
    (e : Finset V) (he : e.card = r) : UniformHypergraph V r where
  edges := insert e H.edges
  uniform := by
    intro f hf
    rcases Finset.mem_insert.mp hf with h | h
    · subst f; exact he
    · exact H.uniform f h

def complete [Fintype V] (r : ℕ) : UniformHypergraph V r where
  edges := Finset.univ.powersetCard r
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp he).2

@[simp] theorem mem_complete [Fintype V] {r : ℕ} {e : Finset V} :
    e ∈ (complete (V := V) r).edges ↔ e.card = r := by
  simp [complete, Finset.mem_powersetCard]

theorem saturated_small_iff_complete [Fintype V] {a r : ℕ}
    (hV : Fintype.card V ≤ a + 1) (H : UniformHypergraph V r) :
    Saturated a H ↔ H.edges = (complete (V := V) r).edges := by
  constructor
  · intro h
    apply Finset.ext
    intro e
    constructor
    · intro he
      exact mem_complete.mpr (H.uniform e he)
    · intro he
      by_contra hn
      exact free_of_vertex_card_le hV (h.2 e (mem_complete.mp he) hn)
  · intro h
    refine ⟨free_of_vertex_card_le hV, ?_⟩
    intro e he hn
    exact False.elim (hn (h ▸ mem_complete.mpr he))

/-- The incidence graph includes all ambient vertices, so it retains isolates. -/
def incidenceGraph (E : Finset (Finset V)) : SimpleGraph (V ⊕ {e // e ∈ E}) where
  Adj x y := match x, y with
    | .inl v, .inr e => v ∈ e.val
    | .inr e, .inl v => v ∈ e.val
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> exact h⟩
  loopless := ⟨by
    intro x
    cases x <;> simp⟩

instance incidenceGraph_decidableAdj (E : Finset (Finset V)) :
    DecidableRel (incidenceGraph E).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [incidenceGraph] <;> infer_instance

@[simp] theorem incidenceGraph_adj_vertex_edge (E : Finset (Finset V))
    (v : V) (e : {e // e ∈ E}) :
    (incidenceGraph E).Adj (.inl v) (.inr e) ↔ v ∈ e.val := Iff.rfl

@[simp] theorem incidenceGraph_adj_edge_vertex (E : Finset (Finset V))
    (e : {e // e ∈ E}) (v : V) :
    (incidenceGraph E).Adj (.inr e) (.inl v) ↔ v ∈ e.val := Iff.rfl

@[simp] theorem incidenceGraph_not_adj_vertex_vertex (E : Finset (Finset V))
    (v w : V) : ¬ (incidenceGraph E).Adj (.inl v) (.inl w) := id

@[simp] theorem incidenceGraph_not_adj_edge_edge (E : Finset (Finset V))
    (e f : {e // e ∈ E}) : ¬ (incidenceGraph E).Adj (.inr e) (.inr f) := id

end Berge
