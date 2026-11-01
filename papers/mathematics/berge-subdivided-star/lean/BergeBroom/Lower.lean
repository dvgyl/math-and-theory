import BergeBroom.Construction
import BergeBroom.Leaves
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge

universe u
variable {V : Type u} [DecidableEq V]

namespace ForestGeometry

theorem common_neighbor_unique {G : SimpleGraph V} (hG : G.IsAcyclic)
    {u v x y : V} (huv : u ≠ v)
    (hux : G.Adj u x) (hxv : G.Adj x v)
    (huy : G.Adj u y) (hyv : G.Adj y v) : x = y := by
  let p : G.Walk u v := .cons hux (.cons hxv .nil)
  let q : G.Walk u v := .cons huy (.cons hyv .nil)
  have hp : p.IsPath := by
    simp [p, SimpleGraph.Walk.isPath_def, hux.ne, hxv.ne, huv]
  have hq : q.IsPath := by
    simp [q, SimpleGraph.Walk.isPath_def, huy.ne, hyv.ne, huv]
  have heq := (hG.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  have hs := congrArg (fun w : G.Path u v => w.val.support) heq
  simpa [p, q] using hs

theorem no_shortcut {G : SimpleGraph V} (hG : G.IsAcyclic)
    {u v w x y z : V}
    (h₁ : G.Adj u v) (h₂ : G.Adj v w)
    (h₃ : G.Adj w x) (h₄ : G.Adj x y)
    (h₅ : G.Adj u z) (h₆ : G.Adj z y)
    (hp : (SimpleGraph.Walk.cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil)))).IsPath)
    (huy : u ≠ y) : False := by
  let p : G.Walk u y := .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil)))
  let q : G.Walk u y := .cons h₅ (.cons h₆ .nil)
  have hq : q.IsPath := by
    simp [q, SimpleGraph.Walk.isPath_def, h₅.ne, h₆.ne, huy]
  have heq := (hG.subsingleton_path u y).elim ⟨p, hp⟩ ⟨q, hq⟩
  have hl := congrArg (fun w : G.Path u y => w.val.length) heq
  simp [p, q] at hl

end ForestGeometry

theorem acyclic_edge_intersection {E : Finset (Finset V)}
    (hE : (incidenceGraph E).IsAcyclic)
    {e f : {e // e ∈ E}} {c b : V} (hcb : c ≠ b)
    (hce : c ∈ e.val) (hbe : b ∈ e.val)
    (hcf : c ∈ f.val) (hbf : b ∈ f.val) : e = f := by
  have h := ForestGeometry.common_neighbor_unique hE
    (u := Sum.inl c) (v := Sum.inl b)
    (x := Sum.inr e) (y := Sum.inr f)
    (by simpa using hcb) hce hbe hcf hbf
  exact Sum.inr.inj h

theorem acyclic_tail_avoids_spokes {E : Finset (Finset V)}
    (hE : (incidenceGraph E).IsAcyclic)
    {e f : {e // e ∈ E}} {c b x : V} (hcb : c ≠ b) (hbx : b ≠ x)
    (hce : c ∈ e.val) (hbe : b ∈ e.val)
    (hbf : b ∈ f.val) (hxf : x ∈ f.val) (hef : e ≠ f) :
    ∀ g : {e // e ∈ E}, c ∈ g.val → x ∉ g.val := by
  have hcf : c ∉ f.val := by
    intro h
    exact hef (acyclic_edge_intersection hE hcb hce hbe h hbf)
  have hcx : c ≠ x := by
    intro h
    exact hcf (h.symm ▸ hxf)
  intro g hcg hxg
  have h₁ : (incidenceGraph E).Adj (.inl c) (.inr e) := hce
  have h₂ : (incidenceGraph E).Adj (.inr e) (.inl b) := hbe
  have h₃ : (incidenceGraph E).Adj (.inl b) (.inr f) := hbf
  have h₄ : (incidenceGraph E).Adj (.inr f) (.inl x) := hxf
  have h₅ : (incidenceGraph E).Adj (.inl c) (.inr g) := hcg
  have h₆ : (incidenceGraph E).Adj (.inr g) (.inl x) := hxg
  apply ForestGeometry.no_shortcut hE h₁ h₂ h₃ h₄ h₅ h₆
  · simp [SimpleGraph.Walk.isPath_def, hcb, hcx, hbx, hef]
  · simpa using hcx

theorem contains_of_acyclic_neighbor {r k : ℕ} (H : UniformHypergraph V r)
    (hr : 2 ≤ r) (hE : (incidenceGraph H.edges).IsAcyclic)
    {c b : V} (hcb : c ≠ b) (hd : k+1 ≤ degree H.edges c)
    (mid tail : {e // e ∈ H.edges}) (hmt : mid ≠ tail)
    (hcm : c ∈ mid.val) (hbm : b ∈ mid.val) (hbt : b ∈ tail.val) :
    ContainsBroom (k+1) H.edges := by
  classical
  have hct : c ∉ tail.val := by
    intro h
    exact hmt (acyclic_edge_intersection hE hcb hcm hbm h hbt)
  have htailcard : 1 < tail.val.card := by rw [H.uniform _ tail.property]; omega
  obtain ⟨x, hxt, hxb⟩ := Finset.exists_mem_ne htailcard b
  have hcx : c ≠ x := by intro h; exact hct (h.symm ▸ hxt)
  have hm : mid.val ∈ incidentEdges H.edges c := mem_incidentEdges.mpr ⟨mid.property,hcm⟩
  have hk : Fintype.card (Fin k) ≤ ((incidentEdges H.edges c).erase mid.val).card := by
    rw [Finset.card_erase_of_mem hm]
    simp only [Fintype.card_fin]
    unfold degree at hd
    omega
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset hk
  have hfmem (i : Fin k) : f i ∈ incidentEdges H.edges c :=
    (Finset.mem_erase.mp (hf ⟨i,rfl⟩)).2
  have hfne (i : Fin k) : f i ≠ mid.val :=
    (Finset.mem_erase.mp (hf ⟨i,rfl⟩)).1
  let ae : Fin k ↪ {e // e ∈ H.edges} :=
    { toFun := fun i => ⟨f i,(mem_incidentEdges.mp (hfmem i)).1⟩
      inj' := by
        intro i j h
        exact f.injective (congrArg Subtype.val h) }
  have hca (i : Fin k) : c ∈ (ae i).val := (mem_incidentEdges.mp (hfmem i)).2
  have ham (i : Fin k) : ae i ≠ mid := by
    intro h
    exact hfne i (congrArg Subtype.val h)
  have hat (i : Fin k) : ae i ≠ tail := by
    intro h
    exact hct (h ▸ hca i)
  have hrep (i : Fin k) : ∃ v ∈ (ae i).val, v ≠ c := by
    apply Finset.exists_mem_ne
    rw [H.uniform _ (ae i).property]
    omega
  choose rep hrmem hrne using hrep
  let arms : Fin k ↪ V :=
    { toFun := rep
      inj' := by
        intro i j h
        apply ae.injective
        apply acyclic_edge_intersection hE (hrne i).symm (hca i) (hrmem i) (hca j)
        exact h ▸ hrmem j }
  have hab (i : Fin k) : arms i ≠ b := by
    intro h
    apply ham i
    exact acyclic_edge_intersection hE hcb (hca i) (h ▸ hrmem i) hcm hbm
  have hax (i : Fin k) : arms i ≠ x := by
    intro h
    exact acyclic_tail_avoids_spokes hE hcb hxb.symm hcm hbm hbt hxt hmt
      (ae i) (hca i) (h ▸ hrmem i)
  exact ⟨broomOfArms c b x arms hcb hcx hxb.symm hrne hab hax
    mid tail ae hmt ham hat hcm hbm hbt hxt hca hrmem⟩

theorem acyclic_free_neighbor_degree {r k : ℕ} (H : UniformHypergraph V r)
    (hr : 2 ≤ r) (hE : (incidenceGraph H.edges).IsAcyclic)
    (hfree : BroomFree (k+1) H.edges) {c b : V} (hcb : c ≠ b)
    (hd : k+1 ≤ degree H.edges c) (mid : {e // e ∈ H.edges})
    (hcm : c ∈ mid.val) (hbm : b ∈ mid.val) : degree H.edges b ≤ 1 := by
  by_contra hn
  have hdeg : 1 < (incidentEdges H.edges b).card := by unfold degree at hn; omega
  obtain ⟨f,hf,hfm⟩ := Finset.exists_mem_ne hdeg mid.val
  have hfE := (mem_incidentEdges.mp hf).1
  have hbf := (mem_incidentEdges.mp hf).2
  let tail : {e // e ∈ H.edges} := ⟨f,hfE⟩
  have hmt : mid ≠ tail := by
    intro h
    exact hfm (congrArg Subtype.val h).symm
  exact hfree (contains_of_acyclic_neighbor H hr hE hcb hd mid tail hmt hcm hbm hbf)

theorem property_of_reachable {W : Type*} {G : SimpleGraph W}
    (P : W → Prop) (hstep : ∀ u v, G.Adj u v → P u → P v)
    {u v : W} (h : G.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons h p ih => exact ih (hstep _ _ h hu)

theorem cone_of_connected_acyclic_free {r k : ℕ} (H : UniformHypergraph V r)
    (hr : 2 ≤ r) (hE : (incidenceGraph H.edges).IsAcyclic)
    (hconn : (incidenceGraph H.edges).Connected)
    (hfree : BroomFree (k+1) H.edges) {c : V} (hd : k+1 ≤ degree H.edges c) :
    (∀ e ∈ H.edges, c ∈ e) ∧ (∀ b, b ≠ c → degree H.edges b ≤ 1) := by
  classical
  let P : (V ⊕ {e // e ∈ H.edges}) → Prop := fun w =>
    match w with
    | Sum.inl v => v=c ∨ ∃ e : {e // e ∈ H.edges}, c ∈ e.val ∧ v ∈ e.val
    | Sum.inr e => c ∈ e.val
  have hstep : ∀ u v, (incidenceGraph H.edges).Adj u v → P u → P v := by
    intro u v huv hu
    cases u with
    | inl b =>
      cases v with
      | inl d => exact False.elim huv
      | inr f =>
        change b ∈ f.val at huv
        change c ∈ f.val
        rcases hu with hbc | ⟨e,hce,hbe⟩
        · exact hbc ▸ huv
        · by_cases hbc : b=c
          · exact hbc ▸ huv
          · have hdeg := acyclic_free_neighbor_degree H hr hE hfree (Ne.symm hbc) hd e hce hbe
            have he : e.val ∈ incidentEdges H.edges b := mem_incidentEdges.mpr ⟨e.property,hbe⟩
            have hf : f.val ∈ incidentEdges H.edges b := mem_incidentEdges.mpr ⟨f.property,huv⟩
            have hef : e.val=f.val := (Finset.card_le_one_iff.mp hdeg) he hf
            exact hef ▸ hce
    | inr e =>
      cases v with
      | inl b => exact Or.inr ⟨e,hu,huv⟩
      | inr f => exact False.elim huv
  have hroot : P (Sum.inl c) := Or.inl rfl
  have hall (w : V ⊕ {e // e ∈ H.edges}) : P w :=
    property_of_reachable P hstep (hconn (Sum.inl c) w) hroot
  constructor
  · intro e he
    exact hall (Sum.inr ⟨e,he⟩)
  · intro b hbc
    rcases hall (Sum.inl b) with h | ⟨e,hce,hbe⟩
    · exact False.elim (hbc h)
    · exact acyclic_free_neighbor_degree H hr hE hfree hbc.symm hd e hce hbe

theorem saturated_tree_is_loose [Fintype V] {r a : ℕ} (H : UniformHypergraph V r)
    (ha : 3 ≤ a) (hr : 3 ≤ r) (hSat : Saturated a H)
    (ht : (incidenceGraph H.edges).IsTree) (hm : 2 ≤ H.edges.card) :
    ∃ c : V, a ≤ degree H.edges c ∧ (∀ e ∈ H.edges, c ∈ e) ∧
      (∀ b, b ≠ c → degree H.edges b ≤ 1) := by
  obtain ⟨c,hc⟩ := saturated_tree_has_high_degree ha hr H hSat ht hm
  have hka : a-1+1=a := by omega
  have hf : BroomFree (a-1+1) H.edges := by simpa only [hka] using hSat.1
  have hd : a-1+1 ≤ degree H.edges c := by simpa only [hka] using hc
  obtain ⟨hcone,hdeg⟩ := cone_of_connected_acyclic_free H (by omega) ht.isAcyclic
    ht.connected hf hd
  exact ⟨c,hc,hcone,hdeg⟩

theorem saturated_tree_edges_ge [Fintype V] {r a : ℕ} (H : UniformHypergraph V r)
    (ha : 3 ≤ a) (hr : 3 ≤ r) (hSat : Saturated a H)
    (ht : (incidenceGraph H.edges).IsTree) (hm : 2 ≤ H.edges.card) :
    a ≤ H.edges.card := by
  obtain ⟨c,hc,_,_⟩ := saturated_tree_is_loose H ha hr hSat ht hm
  exact hc.trans (degree_le_edge_card _ _)

end Berge
