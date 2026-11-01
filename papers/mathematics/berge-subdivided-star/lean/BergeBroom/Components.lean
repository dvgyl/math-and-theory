import BergeBroom.Incidence
import Mathlib.Logic.Equiv.Sum

/-! # Actual hypergraph components and their partition identities -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Berge

open scoped BigOperators

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

abbrev Component (E : Finset (Finset V)) := (incidenceGraph E).ConnectedComponent

instance componentFinite (E : Finset (Finset V)) : Finite (Component E) :=
  Quot.finite _

instance componentFintype (E : Finset (Finset V)) : Fintype (Component E) :=
  Fintype.ofFinite _

instance componentDecidableEq (E : Finset (Finset V)) : DecidableEq (Component E) :=
  Classical.decEq _

abbrev ComponentVertex (E : Finset (Finset V)) (c : Component E) :=
  {v : V // (incidenceGraph E).connectedComponentMk (.inl v) = c}

abbrev ComponentEdge (E : Finset (Finset V)) (c : Component E) :=
  {e : {e // e ∈ E} // (incidenceGraph E).connectedComponentMk (.inr e) = c}

theorem sum_component_vertex_card (E : Finset (Finset V)) :
    ∑ c : Component E, Fintype.card (ComponentVertex E c) = Fintype.card V := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun v : V => (incidenceGraph E).connectedComponentMk (.inl v)))

theorem sum_component_edge_card (E : Finset (Finset V)) :
    ∑ c : Component E, Fintype.card (ComponentEdge E c) = E.card := by
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun e : {e // e ∈ E} => (incidenceGraph E).connectedComponentMk (.inr e)))).trans
      (Fintype.card_coe E)

theorem vertex_component_of_mem (E : Finset (Finset V)) (c : Component E)
    (e : ComponentEdge E c) {v : V} (hv : v ∈ e.val.val) :
    (incidenceGraph E).connectedComponentMk (.inl v) = c :=
  (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (show (incidenceGraph E).Adj (.inl v) (.inr e.val) from hv)).trans e.property

def componentEdge (E : Finset (Finset V)) (c : Component E) (e : ComponentEdge E c) :
    Finset (ComponentVertex E c) :=
  e.val.val.attach.map
    { toFun := fun v => ⟨v.val, vertex_component_of_mem E c e v.property⟩
      inj' := by
        intro v w h
        exact Subtype.ext (congrArg (fun z : ComponentVertex E c => z.val) h) }

@[simp] theorem componentEdge_card (E : Finset (Finset V)) (c : Component E)
    (e : ComponentEdge E c) : (componentEdge E c e).card = e.val.val.card := by
  simp [componentEdge]

@[simp] theorem mem_componentEdge (E : Finset (Finset V)) (c : Component E)
    (e : ComponentEdge E c) (v : ComponentVertex E c) :
    v ∈ componentEdge E c e ↔ v.val ∈ e.val.val := by
  constructor
  · intro h
    obtain ⟨w, _, hw⟩ := Finset.mem_map.mp h
    have hv := congrArg (fun z : ComponentVertex E c => z.val) hw
    rw [← hv]
    exact w.property
  · intro h
    exact Finset.mem_map.mpr ⟨⟨v.val, h⟩, by simp, Subtype.ext rfl⟩

@[simp] theorem componentEdge_image_val (E : Finset (Finset V)) (c : Component E)
    (e : ComponentEdge E c) :
    (componentEdge E c e).image Subtype.val = e.val.val := by
  ext v
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    exact (mem_componentEdge E c e w).mp hw
  · intro h
    exact Finset.mem_image.mpr
      ⟨⟨v, vertex_component_of_mem E c e h⟩, (mem_componentEdge E c e _).mpr h, rfl⟩

theorem componentEdge_injective (E : Finset (Finset V)) (c : Component E) :
    Function.Injective (componentEdge E c) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  have hv := congrArg (fun s : Finset (ComponentVertex E c) => s.image Subtype.val) h
  simpa only [componentEdge_image_val] using hv

def componentEdges (E : Finset (Finset V)) (c : Component E) :
    Finset (Finset (ComponentVertex E c)) :=
  Finset.univ.image (componentEdge E c)

def componentHypergraph {r : ℕ} (H : UniformHypergraph V r) (c : Component H.edges) :
    UniformHypergraph (ComponentVertex H.edges c) r where
  edges := componentEdges H.edges c
  uniform := by
    intro f hf
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hf
    rw [componentEdge_card]
    exact H.uniform e.val.val e.val.property

@[simp] theorem componentHypergraph_edge_card {r : ℕ} (H : UniformHypergraph V r)
    (c : Component H.edges) :
    (componentHypergraph H c).edges.card = Fintype.card (ComponentEdge H.edges c) := by
  exact (Finset.card_image_of_injective Finset.univ
    (componentEdge_injective H.edges c)).trans (Finset.card_univ)

theorem sum_componentHypergraph_edge_card {r : ℕ} (H : UniformHypergraph V r) :
    ∑ c : Component H.edges, (componentHypergraph H c).edges.card = H.edges.card := by
  simp only [componentHypergraph_edge_card]
  exact sum_component_edge_card H.edges

def componentEdgeEquiv (E : Finset (Finset V)) (c : Component E) :
    ComponentEdge E c ≃ {f // f ∈ componentEdges E c} :=
  Equiv.ofBijective
    (fun e => ⟨componentEdge E c e, Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩)
    ⟨by
        intro e f h
        exact componentEdge_injective E c (congrArg Subtype.val h),
      by
        intro f
        obtain ⟨e, _, he⟩ := Finset.mem_image.mp f.property
        exact ⟨e, Subtype.ext he⟩⟩

@[simp] theorem componentEdgeEquiv_apply_val (E : Finset (Finset V)) (c : Component E)
    (e : ComponentEdge E c) :
    ((componentEdgeEquiv E c) e).val = componentEdge E c e := rfl

theorem componentEdgeEquiv_symm_val (E : Finset (Finset V)) (c : Component E)
    (f : {f // f ∈ componentEdges E c}) :
    componentEdge E c ((componentEdgeEquiv E c).symm f) = f.val :=
  congrArg Subtype.val ((componentEdgeEquiv E c).apply_symm_apply f)

def componentNodeEquiv (E : Finset (Finset V)) (c : Component E) :
    (ComponentVertex E c ⊕ {f // f ∈ componentEdges E c}) ≃ c.supp where
  toFun := fun x => match x with
    | .inl v => ⟨.inl v.val, v.property⟩
    | .inr f =>
      ⟨.inr ((componentEdgeEquiv E c).symm f).val,
        ((componentEdgeEquiv E c).symm f).property⟩
  invFun := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | inl v => exact .inl ⟨v, hx⟩
    | inr e => exact .inr ((componentEdgeEquiv E c) ⟨e, hx⟩)
  left_inv := by
    intro x
    cases x with
    | inl v => rfl
    | inr f => exact congrArg Sum.inr ((componentEdgeEquiv E c).apply_symm_apply f)
  right_inv := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | inl v => rfl
    | inr e =>
      apply Subtype.ext
      exact congrArg (fun z : ComponentEdge E c => Sum.inr z.val)
        ((componentEdgeEquiv E c).symm_apply_apply ⟨e, hx⟩)

def componentIncidenceIso (E : Finset (Finset V)) (c : Component E) :
    incidenceGraph (componentEdges E c) ≃g (incidenceGraph E).induce c.supp where
  toEquiv := componentNodeEquiv E c
  map_rel_iff' := by
    intro x y
    cases x with
    | inl v =>
      cases y with
      | inl w => rfl
      | inr f =>
        change v.val ∈ ((componentEdgeEquiv E c).symm f).val.val ↔ v ∈ f.val
        rw [← componentEdgeEquiv_symm_val E c f, mem_componentEdge]
    | inr f =>
      cases y with
      | inl v =>
        change v.val ∈ ((componentEdgeEquiv E c).symm f).val.val ↔ v ∈ f.val
        rw [← componentEdgeEquiv_symm_val E c f, mem_componentEdge]
      | inr g => rfl

theorem componentHypergraph_connected {r : ℕ} (H : UniformHypergraph V r)
    (c : Component H.edges) :
    (incidenceGraph (componentHypergraph H c).edges).Connected :=
  (componentIncidenceIso H.edges c).connected_iff.mpr (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).1

theorem component_vertex_bound {r : ℕ} (hr : 1 ≤ r) (H : UniformHypergraph V r)
    (c : Component H.edges) :
    Fintype.card (ComponentVertex H.edges c) ≤
      (r - 1) * (componentHypergraph H c).edges.card + 1 :=
  connected_vertex_bound hr (componentHypergraph H c) (componentHypergraph_connected H c)

theorem BroomCopy.labels_eq_center {a : ℕ} {E : Finset (Finset V)}
    (C : BroomCopy a E) {β : Type*} (label : V → β)
    (h : ∀ e ∈ E, ∀ v ∈ e, ∀ w ∈ e, label v = label w) (j : Fin (a + 2)) :
    label (C.core j) = label (C.core 0) := by
  have hs : label (C.core (stemVertex a)) = label (C.core 0) := by
    apply h _ (C.edge 0).property
    · simpa [broomRight, stemVertex] using C.right_mem 0
    · simpa [broomLeft] using C.left_mem 0
  have hl (i : Fin (a + 1)) : label (C.core (broomLeft a i)) = label (C.core 0) := by
    by_cases hi : i.val = 1
    · simpa [broomLeft, hi, stemVertex] using hs
    · simp [broomLeft, hi]
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    rfl
  · let i : Fin (a + 1) := ⟨j.val - 1, by omega⟩
    have he : broomRight a i = j := by
      apply Fin.ext
      dsimp [broomRight, i]
      omega
    rw [← he]
    exact (h _ (C.edge i).property _ (C.right_mem i) _ (C.left_mem i)).trans (hl i)

@[simp] theorem mem_component_project (E : Finset (Finset V)) (c : Component E)
    (S : Finset (ComponentVertex E c)) (v : ComponentVertex E c) :
    v.val ∈ S.image Subtype.val ↔ v ∈ S := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
    have : w = v := Subtype.ext he
    simpa [this] using hw
  · intro h
    exact Finset.mem_image.mpr ⟨v, h, rfl⟩

theorem component_project_label (E : Finset (Finset V)) (c : Component E)
    (S : Finset (ComponentVertex E c)) {v : V} (hv : v ∈ S.image Subtype.val) :
    (incidenceGraph E).connectedComponentMk (.inl v) = c := by
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact w.property

def componentLiftSet (E : Finset (Finset V)) (c : Component E) (S : Finset V) :
    Finset (ComponentVertex E c) := Finset.univ.filter (fun v => v.val ∈ S)

@[simp] theorem mem_componentLiftSet (E : Finset (Finset V)) (c : Component E)
    (S : Finset V) (v : ComponentVertex E c) :
    v ∈ componentLiftSet E c S ↔ v.val ∈ S := by simp [componentLiftSet]

theorem componentLiftSet_project (E : Finset (Finset V)) (c : Component E)
    (S : Finset (ComponentVertex E c)) :
    componentLiftSet E c (S.image Subtype.val) = S := by
  ext v
  simp only [mem_componentLiftSet, mem_component_project]

theorem componentLiftSet_image_val (E : Finset (Finset V)) (c : Component E)
    (S : Finset V)
    (hS : ∀ v ∈ S, (incidenceGraph E).connectedComponentMk (.inl v) = c) :
    (componentLiftSet E c S).image Subtype.val = S := by
  ext v
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    exact (mem_componentLiftSet E c S w).mp hw
  · intro h
    exact Finset.mem_image.mpr
      ⟨⟨v, hS v h⟩, (mem_componentLiftSet E c S _).mpr h, rfl⟩

theorem component_project_edge_mem (E : Finset (Finset V)) (c : Component E)
    {f : Finset (ComponentVertex E c)} (hf : f ∈ componentEdges E c) :
    f.image Subtype.val ∈ E := by
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hf
  simpa only [componentEdge_image_val] using e.val.property

theorem componentHypergraph_free {a r : ℕ} (H : UniformHypergraph V r)
    (hfree : BroomFree a H.edges) (c : Component H.edges) :
    BroomFree a (componentHypergraph H c).edges := by
  rintro ⟨C⟩
  apply hfree
  refine ⟨C.mapVerticesInto ⟨Subtype.val, Subtype.val_injective⟩ ?_⟩
  intro e he
  simpa [Finset.map_eq_image] using component_project_edge_mem H.edges c he

theorem component_missing_projects (E : Finset (Finset V)) (c : Component E)
    (S : Finset (ComponentVertex E c)) (hS : S.Nonempty)
    (hn : S ∉ componentEdges E c) : S.image Subtype.val ∉ E := by
  intro he
  obtain ⟨v, hv⟩ := hS
  have hve : v.val ∈ S.image Subtype.val := (mem_component_project E c S v).mpr hv
  have hc : (incidenceGraph E).connectedComponentMk
      (.inr (⟨S.image Subtype.val, he⟩ : {e // e ∈ E})) = c :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (incidenceGraph E).Adj (.inl v.val)
        (.inr (⟨S.image Subtype.val, he⟩ : {e // e ∈ E})) from hve)).symm.trans v.property
  let e : ComponentEdge E c := ⟨⟨S.image Subtype.val, he⟩, hc⟩
  have hEq : componentEdge E c e = S := by
    ext w
    exact (mem_componentEdge E c e w).trans (mem_component_project E c S w)
  exact hn (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, hEq⟩)

theorem componentHypergraph_saturated {a r : ℕ} (hr : 1 ≤ r)
    (H : UniformHypergraph V r) (hsat : Saturated a H) (c : Component H.edges) :
    Saturated a (componentHypergraph H c) := by
  refine ⟨componentHypergraph_free H hsat.1 c, ?_⟩
  intro S hS hn
  have hpos : S.Nonempty := Finset.card_pos.mp (by omega)
  let T : Finset V := S.image Subtype.val
  have hT : T.card = r := by
    rw [Finset.card_image_of_injective S Subtype.val_injective]
    exact hS
  have hnT : T ∉ H.edges := component_missing_projects H.edges c S hpos hn
  obtain ⟨C⟩ := hsat.2 T hT hnT
  let label : V → Component H.edges := fun v =>
    (incidenceGraph H.edges).connectedComponentMk (.inl v)
  have hlabel : ∀ f ∈ insert T H.edges, ∀ v ∈ f, ∀ w ∈ f, label v = label w := by
    intro f hf v hv w hw
    rcases Finset.mem_insert.mp hf with he | he
    · subst f
      exact (component_project_label H.edges c S hv).trans
        (component_project_label H.edges c S hw).symm
    · let ef : {e // e ∈ H.edges} := ⟨f, he⟩
      have hv' := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (incidenceGraph H.edges).Adj (.inl v) (.inr ef) from hv)
      have hw' := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (incidenceGraph H.edges).Adj (.inl w) (.inr ef) from hw)
      exact hv'.trans hw'.symm
  obtain ⟨i₀, hi₀⟩ := C.uses_inserted_edge hsat.1
  have hcenter : label (C.core 0) = c := by
    have hmem : C.core (broomLeft a i₀) ∈ T := by simpa [hi₀] using C.left_mem i₀
    exact (C.labels_eq_center label hlabel (broomLeft a i₀)).symm.trans
      (component_project_label H.edges c S hmem)
  have hcore (j : Fin (a + 2)) : label (C.core j) = c :=
    (C.labels_eq_center label hlabel j).trans hcenter
  have hedge (i : Fin (a + 1)) (he : (C.edge i).val ∈ H.edges) :
      (incidenceGraph H.edges).connectedComponentMk
        (.inr (⟨(C.edge i).val, he⟩ : {e // e ∈ H.edges})) = c :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (incidenceGraph H.edges).Adj (.inl (C.core (broomLeft a i)))
        (.inr (⟨(C.edge i).val, he⟩ : {e // e ∈ H.edges})) from C.left_mem i)).symm.trans
          (hcore (broomLeft a i))
  have hsub (i : Fin (a + 1)) (v : V) (hv : v ∈ (C.edge i).val) : label v = c := by
    rcases Finset.mem_insert.mp (C.edge i).property with he | he
    · rw [he] at hv
      exact component_project_label H.edges c S hv
    · exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (incidenceGraph H.edges).Adj (.inl v)
          (.inr (⟨(C.edge i).val, he⟩ : {e // e ∈ H.edges})) from hv)).trans (hedge i he)
  have hmem (i : Fin (a + 1)) :
      componentLiftSet H.edges c (C.edge i).val ∈
        insert S (componentHypergraph H c).edges := by
    rcases Finset.mem_insert.mp (C.edge i).property with he | he
    · apply Finset.mem_insert.mpr
      left
      rw [he]
      exact componentLiftSet_project H.edges c S
    · let ef : ComponentEdge H.edges c := ⟨⟨(C.edge i).val, he⟩, hedge i he⟩
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨ef, Finset.mem_univ ef, ?_⟩
      ext v
      simp only [mem_componentEdge, mem_componentLiftSet]
      rfl
  refine ⟨{
    core :=
      { toFun := fun j => ⟨C.core j, hcore j⟩
        inj' := by
          intro i j hij
          exact C.core.injective
            (congrArg (fun v : ComponentVertex H.edges c => v.val) hij) }
    edge :=
      { toFun := fun i => ⟨componentLiftSet H.edges c (C.edge i).val, hmem i⟩
        inj' := by
          intro i j hij
          apply C.edge.injective
          apply Subtype.ext
          have hval := congrArg
            (fun f : {f // f ∈ insert S (componentHypergraph H c).edges} =>
              f.val.image Subtype.val) hij
          dsimp only at hval
          rw [componentLiftSet_image_val H.edges c _ (hsub i),
            componentLiftSet_image_val H.edges c _ (hsub j)] at hval
          exact hval }
    left_mem := fun i => (mem_componentLiftSet H.edges c _ _).mpr (C.left_mem i)
    right_mem := fun i => (mem_componentLiftSet H.edges c _ _).mpr (C.right_mem i) }⟩

theorem componentHypergraph_degree {r : ℕ} (H : UniformHypergraph V r)
    (c : Component H.edges) (v : ComponentVertex H.edges c) :
    degree (componentHypergraph H c).edges v = degree H.edges v.val := by
  let f : {e // e ∈ incidentEdges (componentHypergraph H c).edges v} →
      {e // e ∈ incidentEdges H.edges v.val} := fun e =>
    ⟨e.val.image Subtype.val, mem_incidentEdges.mpr
      ⟨component_project_edge_mem H.edges c (mem_incidentEdges.mp e.property).1,
        (mem_component_project H.edges c e.val v).mpr (mem_incidentEdges.mp e.property).2⟩⟩
  have hinj : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    apply Finset.image_injective Subtype.val_injective
    exact congrArg (fun z : {e // e ∈ incidentEdges H.edges v.val} => z.val) h
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨he, hv⟩ := mem_incidentEdges.mp e.property
    have hc : (incidenceGraph H.edges).connectedComponentMk
        (.inr (⟨e.val, he⟩ : {e // e ∈ H.edges})) = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (incidenceGraph H.edges).Adj (.inl v.val)
          (.inr (⟨e.val, he⟩ : {e // e ∈ H.edges})) from hv)).symm.trans v.property
    let ef : ComponentEdge H.edges c := ⟨⟨e.val, he⟩, hc⟩
    let g : {e // e ∈ incidentEdges (componentHypergraph H c).edges v} :=
      ⟨componentEdge H.edges c ef, mem_incidentEdges.mpr
        ⟨Finset.mem_image.mpr ⟨ef, Finset.mem_univ ef, rfl⟩,
          (mem_componentEdge H.edges c ef v).mpr hv⟩⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact componentEdge_image_val H.edges c ef
  exact (Fintype.card_coe _).symm.trans
    ((Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).trans (Fintype.card_coe _))

theorem component_vertex_card_of_edge_zero {r : ℕ} (hr : 1 ≤ r)
    (H : UniformHypergraph V r) (c : Component H.edges)
    (hm : (componentHypergraph H c).edges.card = 0) :
    Fintype.card (ComponentVertex H.edges c) = 1 := by
  have hu := component_vertex_bound hr H c
  rw [hm, mul_zero, zero_add] at hu
  have hc := componentHypergraph_connected H c
  let _ := hc.nonempty
  have hp : 0 < Fintype.card
      (ComponentVertex H.edges c ⊕ {e // e ∈ (componentHypergraph H c).edges}) :=
    Fintype.card_pos
  simp only [Fintype.card_sum, Fintype.card_coe, hm, add_zero] at hp
  omega

theorem component_vertex_card_of_edge_one {r : ℕ} (hr : 1 ≤ r)
    (H : UniformHypergraph V r) (c : Component H.edges)
    (hm : (componentHypergraph H c).edges.card = 1) :
    Fintype.card (ComponentVertex H.edges c) = r := by
  have hu := component_vertex_bound hr H c
  rw [hm, mul_one, Nat.sub_add_cancel hr] at hu
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (componentHypergraph H c).edges.card by omega)
  have hl : r ≤ Fintype.card (ComponentVertex H.edges c) := by
    calc
      r = e.card := ((componentHypergraph H c).uniform e he).symm
      _ ≤ Fintype.card (ComponentVertex H.edges c) := Finset.card_le_univ e
  omega

theorem reachable_eq_of_degree_zero {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {v w : W}
    (hd : G.degree v = 0) (h : G.Reachable v w) : v = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hvx p =>
    have hp : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨_, hvx⟩
    omega

theorem component_edge_zero_of_degree_zero {r : ℕ} (H : UniformHypergraph V r)
    (v : V) (hd : degree H.edges v = 0) :
    (componentHypergraph H ((incidenceGraph H.edges).connectedComponentMk (.inl v))).edges.card = 0 := by
  rw [componentHypergraph_edge_card, Fintype.card_eq_zero_iff]
  refine ⟨fun e => ?_⟩
  have hr : (incidenceGraph H.edges).Reachable (.inl v) (.inr e.val) :=
    SimpleGraph.ConnectedComponent.exact e.property.symm
  have hd' : (incidenceGraph H.edges).degree (.inl v) = 0 := by simpa using hd
  have he := reachable_eq_of_degree_zero (incidenceGraph H.edges) hd' hr
  cases he

theorem zero_component_count {r : ℕ} (hr : 1 ≤ r) (H : UniformHypergraph V r) :
    (Finset.univ.filter (fun c : Component H.edges =>
      (componentHypergraph H c).edges.card = 0)).card =
      (Finset.univ.filter (fun v : V => degree H.edges v = 0)).card := by
  symm
  refine Finset.card_bij
    (fun v _ => (incidenceGraph H.edges).connectedComponentMk (.inl v)) ?_ ?_ ?_
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      component_edge_zero_of_degree_zero H v (Finset.mem_filter.mp hv).2⟩
  · intro v hv w hw he
    have hd : (incidenceGraph H.edges).degree (.inl v) = 0 := by
      simpa using (Finset.mem_filter.mp hv).2
    have hEq := reachable_eq_of_degree_zero (incidenceGraph H.edges) hd
      (SimpleGraph.ConnectedComponent.exact he)
    exact Sum.inl_injective hEq
  · intro c hc
    have hm := (Finset.mem_filter.mp hc).2
    have hp : 0 < Fintype.card (ComponentVertex H.edges c) := by
      rw [component_vertex_card_of_edge_zero hr H c hm]
      omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hp
    have hv : degree H.edges v.val = 0 := by
      have hd := degree_le_edge_card (componentHypergraph H c).edges v
      rw [componentHypergraph_degree, hm] at hd
      omega
    exact ⟨v.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, v.property⟩

theorem component_edge_one_isolated {r : ℕ} (H : UniformHypergraph V r)
    (c : Component H.edges) (hm : (componentHypergraph H c).edges.card = 1)
    (e : ComponentEdge H.edges c) : ∀ v ∈ e.val.val, degree H.edges v = 1 := by
  intro v hv
  let w : ComponentVertex H.edges c := ⟨v, vertex_component_of_mem H.edges c e hv⟩
  have hu := degree_le_edge_card (componentHypergraph H c).edges w
  rw [componentHypergraph_degree, hm] at hu
  have hp : 0 < degree H.edges v := Finset.card_pos.mpr
    ⟨e.val.val, mem_incidentEdges.mpr ⟨e.val.property, hv⟩⟩
  change degree H.edges v ≤ 1 at hu
  omega

theorem isolated_edge_reachable_eq (E : Finset (Finset V)) (e f : {e // e ∈ E})
    (he : ∀ v ∈ e.val, degree E v = 1)
    (hr : (incidenceGraph E).Reachable (.inr e) (.inr f)) : f.val = e.val := by
  let P : V ⊕ {e // e ∈ E} → Prop := fun x => match x with
    | .inl v => v ∈ e.val
    | .inr g => g.val = e.val
  have step {x y : V ⊕ {e // e ∈ E}} (hxy : (incidenceGraph E).Adj x y) : P x → P y := by
    cases x with
    | inl v =>
      cases y with
      | inl w => exact False.elim hxy
      | inr g =>
        intro hv
        have hc : (incidentEdges E v).card ≤ 1 := (he v hv).le
        exact (Finset.card_le_one.mp hc)
          g.val
          (mem_incidentEdges.mpr ⟨g.property, hxy⟩)
          e.val
          (mem_incidentEdges.mpr ⟨e.property, hv⟩)
    | inr g =>
      cases y with
      | inl v =>
        intro hg
        change v ∈ e.val
        change v ∈ g.val at hxy
        change g.val = e.val at hg
        simpa [hg] using hxy
      | inr h => exact False.elim hxy
  have walk_preserves {x y : V ⊕ {e // e ∈ E}} (p : (incidenceGraph E).Walk x y) : P x → P y := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hx => ih (step h hx)
  obtain ⟨p⟩ := hr
  exact walk_preserves p rfl

theorem component_edge_one_of_isolated {r : ℕ} (H : UniformHypergraph V r)
    (e : {e // e ∈ H.edges}) (he : ∀ v ∈ e.val, degree H.edges v = 1) :
    (componentHypergraph H ((incidenceGraph H.edges).connectedComponentMk (.inr e))).edges.card = 1 := by
  rw [componentHypergraph_edge_card]
  let c : Component H.edges := (incidenceGraph H.edges).connectedComponentMk (.inr e)
  have hEq (f : ComponentEdge H.edges c) : f.val.val = e.val :=
    isolated_edge_reachable_eq H.edges e f.val he
      (SimpleGraph.ConnectedComponent.exact f.property.symm)
  let _ : Subsingleton (ComponentEdge H.edges c) :=
    ⟨fun f g => Subtype.ext (Subtype.ext ((hEq f).trans (hEq g).symm))⟩
  let _ : Nonempty (ComponentEdge H.edges c) := ⟨⟨e, rfl⟩⟩
  have hl : Fintype.card (ComponentEdge H.edges c) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hp : 0 < Fintype.card (ComponentEdge H.edges c) := Fintype.card_pos
  change Fintype.card (ComponentEdge H.edges c) = 1
  omega

theorem one_component_count {r : ℕ} (H : UniformHypergraph V r) :
    (Finset.univ.filter (fun c : Component H.edges =>
      (componentHypergraph H c).edges.card = 1)).card =
      (H.edges.filter (fun e => ∀ v ∈ e, degree H.edges v = 1)).card := by
  classical
  symm
  refine Finset.card_bij
    (fun e he => (incidenceGraph H.edges).connectedComponentMk
      (.inr (⟨e, (Finset.mem_filter.mp he).1⟩ : {e // e ∈ H.edges}))) ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      component_edge_one_of_isolated H ⟨e, (Finset.mem_filter.mp he).1⟩
        (Finset.mem_filter.mp he).2⟩
  · intro e he f hf hEq
    exact (isolated_edge_reachable_eq H.edges
      ⟨e, (Finset.mem_filter.mp he).1⟩ ⟨f, (Finset.mem_filter.mp hf).1⟩
        (Finset.mem_filter.mp he).2 (SimpleGraph.ConnectedComponent.exact hEq)).symm
  · intro c hc
    have hm := (Finset.mem_filter.mp hc).2
    have hp : 0 < Fintype.card (ComponentEdge H.edges c) := by
      rw [← componentHypergraph_edge_card H c, hm]
      omega
    obtain ⟨e⟩ := Fintype.card_pos_iff.mp hp
    exact ⟨e.val.val, Finset.mem_filter.mpr
      ⟨e.val.property, component_edge_one_isolated H c hm e⟩, e.property⟩

end Berge
