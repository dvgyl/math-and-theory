import BergeBroom.Definitions

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge
universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]

def mappedEdges (f : V ≃ W) (E : Finset (Finset V)) : Finset (Finset W) :=
  f.finsetCongr.finsetCongr E

@[simp] theorem mappedEdges_card (f : V ≃ W) (E : Finset (Finset V)) :
    (mappedEdges f E).card=E.card := by simp [mappedEdges]

@[simp] theorem mem_mappedEdges (f : V ≃ W) (E : Finset (Finset V)) (e : Finset W) :
    e∈mappedEdges f E ↔ f.symm.finsetCongr e∈E := by
  exact Finset.mem_map_equiv

@[simp] theorem mappedEdges_symm (f : V ≃ W) (E : Finset (Finset V)) :
    mappedEdges f.symm (mappedEdges f E)=E := by
  change f.finsetCongr.finsetCongr.symm (f.finsetCongr.finsetCongr E)=E
  exact f.finsetCongr.finsetCongr.symm_apply_apply E

@[simp] theorem mappedEdges_insert (f : V ≃ W) (E : Finset (Finset V)) (e : Finset V) :
    mappedEdges f (insert e E)=insert (f.finsetCongr e) (mappedEdges f E) := by
  simp [mappedEdges]

def BroomCopy.mapEquiv {a : ℕ} {E : Finset (Finset V)} (B : BroomCopy a E)
    (f : V ≃ W) : BroomCopy a (mappedEdges f E) where
  core := B.core.trans f.toEmbedding
  edge :=
    { toFun := fun i => ⟨f.finsetCongr (B.edge i).val, by
        apply (mem_mappedEdges f E _).mpr
        change f.finsetCongr.symm (f.finsetCongr (B.edge i).val) ∈ E
        rw [f.finsetCongr.symm_apply_apply]
        exact (B.edge i).property⟩
      inj' := by
        intro i j h
        apply B.edge.injective
        apply Subtype.ext
        exact f.finsetCongr.injective (congrArg Subtype.val h) }
  left_mem := by
    intro i
    change f (B.core (broomLeft a i)) ∈ ((B.edge i).val).map f.toEmbedding
    exact Finset.mem_map.mpr ⟨B.core (broomLeft a i),B.left_mem i,rfl⟩
  right_mem := by
    intro i
    change f (B.core (broomRight a i)) ∈ ((B.edge i).val).map f.toEmbedding
    exact Finset.mem_map.mpr ⟨B.core (broomRight a i),B.right_mem i,rfl⟩

theorem contains_mapped_iff {a : ℕ} (f : V ≃ W) (E : Finset (Finset V)) :
    ContainsBroom a (mappedEdges f E) ↔ ContainsBroom a E := by
  constructor
  · rintro ⟨B⟩
    have h : ContainsBroom a (mappedEdges f.symm (mappedEdges f E)) := ⟨B.mapEquiv f.symm⟩
    simpa using h
  · rintro ⟨B⟩
    exact ⟨B.mapEquiv f⟩

def UniformHypergraph.mapEquiv {r : ℕ} (H : UniformHypergraph V r) (f : V ≃ W) :
    UniformHypergraph W r where
  edges := mappedEdges f H.edges
  uniform := by
    intro e he
    have h := H.uniform (f.symm.finsetCongr e) ((mem_mappedEdges f H.edges e).mp he)
    simpa using h

@[simp] theorem mapEquiv_edges_card {r : ℕ} (H : UniformHypergraph V r) (f : V ≃ W) :
    (H.mapEquiv f).edges.card=H.edges.card := mappedEdges_card f H.edges

theorem Saturated.mapEquiv {a r : ℕ} {H : UniformHypergraph V r}
    (h : Saturated a H) (f : V ≃ W) : Saturated a (H.mapEquiv f) := by
  constructor
  · intro hc
    exact h.1 ((contains_mapped_iff f H.edges).mp hc)
  · intro e he hn
    have he' : (f.symm.finsetCongr e).card=r := by simpa using he
    have hn' : f.symm.finsetCongr e∉H.edges := by
      intro hm
      exact hn ((mem_mappedEdges f H.edges e).mpr hm)
    obtain ⟨B⟩ := h.2 (f.symm.finsetCongr e) he' hn'
    have hc : ContainsBroom a (mappedEdges f (insert (f.symm.finsetCongr e) H.edges)) :=
      ⟨B.mapEquiv f⟩
    rw [mappedEdges_insert] at hc
    have heq : f.finsetCongr (f.symm.finsetCongr e)=e :=
      f.finsetCongr.apply_symm_apply e
    rw [heq] at hc
    exact hc

end Berge
