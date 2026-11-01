import BergeBroom.Definitions
import BergeBroom.ComponentClasses

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Berge
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

def isolatedVertices (E : Finset (Finset V)) : Finset V :=
  Finset.univ.filter (fun v => degree E v=0)

def isolatedEdges (E : Finset (Finset V)) : Finset (Finset V) :=
  E.filter (fun e => ∀ v∈e, degree E v=1)

@[simp] theorem mem_isolatedVertices {E : Finset (Finset V)} {v : V} :
    v∈isolatedVertices E ↔ degree E v=0 := by simp [isolatedVertices]

@[simp] theorem mem_isolatedEdges {E : Finset (Finset V)} {e : Finset V} :
    e∈isolatedEdges E ↔ e∈E ∧ ∀v∈e,degree E v=1 := by simp [isolatedEdges]

theorem degree_pos_of_mem {E : Finset (Finset V)} {e : Finset V} {v : V}
    (he : e∈E) (hv : v∈e) : 0<degree E v :=
  Finset.card_pos.mpr ⟨e,mem_incidentEdges.mpr ⟨he,hv⟩⟩

theorem zero_degree_not_mem {E : Finset (Finset V)} {v : V}
    (hv : degree E v=0) {e : Finset V} (he : e∈E) : v∉e := by
  intro hm
  have := degree_pos_of_mem he hm
  omega

theorem degree_one_edge_unique {E : Finset (Finset V)} {v : V}
    (hv : degree E v≤1) {e f : Finset V} (he : e∈E) (hf : f∈E)
    (hve : v∈e) (hvf : v∈f) : e=f :=
  Finset.card_le_one.mp hv e (mem_incidentEdges.mpr ⟨he,hve⟩)
    f (mem_incidentEdges.mpr ⟨hf,hvf⟩)

theorem inserted_edge_left_degree {a : ℕ} (ha : 2≤a)
    {E : Finset (Finset V)} (B : BroomCopy a E) (i : Fin (a+1)) :
    2≤degree E (B.core (broomLeft a i)) := by
  by_cases hi : i.val=1
  · simpa [broomLeft,hi,stemVertex] using B.stem_degree_le (by omega)
  · simpa [broomLeft,hi] using ha.trans B.center_degree_le

/-- A new edge supported on degree-at-most-one vertices, all of whose old
neighbors also have degree at most one, cannot create this broom. -/
theorem free_insert_low_neighbors {a : ℕ} (ha : 3≤a)
    {E : Finset (Finset V)} (hfree : BroomFree a E) (T : Finset V)
    (hdeg : ∀v∈T,degree E v≤1)
    (hnbr : ∀v∈T,∀e∈E,v∈e→∀w∈e,degree E w≤1) :
    BroomFree a (insert T E) := by
  rintro ⟨B⟩
  obtain ⟨i,hi⟩ := B.uses_inserted_edge hfree
  have hleft : B.core (broomLeft a i)∈T := by
    simpa only [hi] using B.left_mem i
  by_cases hii : i.val=1
  · have hstem : B.core (stemVertex a)∈T := by
      simpa [broomLeft,hii,stemVertex] using hleft
    have hne : (B.edge 0).val≠T := by
      intro hh
      have heq : B.edge 0=B.edge i := Subtype.ext (hh.trans hi.symm)
      have hh' := congrArg Fin.val (B.edge.injective heq)
      simp at hh'
      omega
    have hmid : (B.edge 0).val∈E :=
      (Finset.mem_insert.mp (B.edge 0).property).resolve_left hne
    have hsc : B.core (stemVertex a)∈(B.edge 0).val := by
      simpa [broomRight,stemVertex] using B.right_mem 0
    have hcc : B.core 0∈(B.edge 0).val := by
      simpa [broomLeft] using B.left_mem 0
    have hc := hnbr _ hstem _ hmid hsc _ hcc
    have ha' := B.center_degree_le
    have hb := degree_insert_le E T (B.core 0)
    omega
  · have hcT : B.core 0∈T := by simpa [broomLeft,hii] using hleft
    have hc := hdeg _ hcT
    have ha' := B.center_degree_le
    have hb := degree_insert_le E T (B.core 0)
    omega

theorem saturated_isolatedVertices_card {a r : ℕ} (ha : 3≤a) (hr : 3≤r)
    (H : UniformHypergraph V r) (hSat : Saturated a H) :
    (isolatedVertices H.edges).card≤r-1 := by
  classical
  by_contra hn
  have hlarge : r≤(isolatedVertices H.edges).card := by omega
  obtain ⟨T,hsub,hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hzero (v : V) (hv : v∈T) : degree H.edges v=0 :=
    mem_isolatedVertices.mp (hsub hv)
  have hmissing : T∉H.edges := by
    intro hmem
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<T.card by omega)
    exact zero_degree_not_mem (hzero v hv) hmem hv
  have hf := free_insert_low_neighbors ha hSat.1 T
    (fun v hv => by rw [hzero v hv]; omega)
    (by
      intro v hv e he hve w hw
      exact False.elim (zero_degree_not_mem (hzero v hv) he hve))
  exact hf (hSat.2 T hcard hmissing)

theorem isolated_edge_neighbors {E : Finset (Finset V)} {e : Finset V}
    (he : e∈isolatedEdges E) {v : V} (hv : v∈e) :
    degree E v≤1 ∧ ∀f∈E,v∈f→∀w∈f,degree E w≤1 := by
  obtain ⟨he,hleaf⟩ := mem_isolatedEdges.mp he
  constructor
  · rw [hleaf v hv]
  · intro f hf hvf w hw
    have hfe : f=e := degree_one_edge_unique (by rw [hleaf v hv]) hf he hvf hv
    subst f
    rw [hleaf w hw]

/-- Saturation forbids any further isolated or isolated-edge vertex outside an
isolated edge; replacing one vertex of that edge gives a harmless missing edge. -/
theorem isolated_edge_forbids_low_vertex {a r : ℕ} (ha : 3≤a) (hr : 3≤r)
    (H : UniformHypergraph V r) (hSat : Saturated a H)
    {e : Finset V} (he : e∈isolatedEdges H.edges) {y : V} (hy : y∉e)
    (hdy : degree H.edges y≤1)
    (hny : ∀f∈H.edges,y∈f→∀w∈f,degree H.edges w≤1) : False := by
  classical
  have heE := (mem_isolatedEdges.mp he).1
  have hecard := H.uniform e heE
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<e.card by omega)
  let T := insert y (e.erase x)
  have hTcard : T.card=r := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem (fun h => hy (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hx,hecard]
    omega
  have hnempty : (e.erase x).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hx,hecard]
    omega
  obtain ⟨v,hv⟩ := hnempty
  have hve : v∈e := Finset.mem_of_mem_erase hv
  have hmissing : T∉H.edges := by
    intro hmem
    have hvT : v∈T := Finset.mem_insert_of_mem hv
    have hd := (isolated_edge_neighbors he hve).1
    have hTe : T=e := degree_one_edge_unique hd hmem heE hvT hve
    have hyT : y∈T := Finset.mem_insert_self _ _
    exact hy (hTe ▸ hyT)
  have hfree := free_insert_low_neighbors ha hSat.1 T
    (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hdy
      · exact (isolated_edge_neighbors he (Finset.mem_of_mem_erase hv)).1)
    (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hny
      · exact (isolated_edge_neighbors he (Finset.mem_of_mem_erase hv)).2)
  exact hfree (hSat.2 T hTcard hmissing)

theorem saturated_isolatedEdge_no_isolates {a r : ℕ} (ha : 3≤a) (hr : 3≤r)
    (H : UniformHypergraph V r) (hSat : Saturated a H)
    {e : Finset V} (he : e∈isolatedEdges H.edges) :
    isolatedVertices H.edges=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hz := mem_isolatedVertices.mp hy
  exact isolated_edge_forbids_low_vertex ha hr H hSat he
    (zero_degree_not_mem hz (mem_isolatedEdges.mp he).1) (by omega)
    (by intro f hf hyf; exact False.elim (zero_degree_not_mem hz hf hyf))

theorem saturated_isolatedEdges_card {a r : ℕ} (ha : 3≤a) (hr : 3≤r)
    (H : UniformHypergraph V r) (hSat : Saturated a H) :
    (isolatedEdges H.edges).card≤1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  have hfcard := H.uniform f (mem_isolatedEdges.mp hf).1
  obtain ⟨y,hyf⟩ := Finset.card_pos.mp (show 0<f.card by omega)
  have hy : y∉e := by
    intro hye
    have hydeg := (isolated_edge_neighbors hf hyf).1
    exact hne (degree_one_edge_unique hydeg (mem_isolatedEdges.mp he).1
      (mem_isolatedEdges.mp hf).1 hye hyf)
  exact isolated_edge_forbids_low_vertex ha hr H hSat he hy
    (isolated_edge_neighbors hf hyf).1 (isolated_edge_neighbors hf hyf).2

theorem free_insert_at_looseRoot {a : ℕ} (ha : 2≤a)
    {E : Finset (Finset V)} (hfree : BroomFree a E) (c : V) (T : Finset V)
    (hT : ∀v∈T,v=c ∨ degree E v=0)
    (hc : ∀e∈E,c∈e→∀v∈e,v≠c→degree E v≤1) :
    BroomFree a (insert T E) := by
  have high_T (v : V) (hv : v∈T) (hd : 2≤degree (insert T E) v) : v=c := by
    rcases hT v hv with h | h
    · exact h
    · have hb := degree_insert_le E T v
      omega
  have neighbor_after (e : Finset V) (he : e∈E) (hce : c∈e)
      (v : V) (hv : v∈e) (hvc : v≠c) : degree (insert T E) v≤1 := by
    have hvT : v∉T := by
      intro hvT
      rcases hT v hvT with h | h
      · exact hvc h
      · exact zero_degree_not_mem h he hv
    rw [degree_insert_of_not_mem E T v hvT]
    exact hc e he hce v hv hvc
  rintro ⟨B⟩
  obtain ⟨i,hi⟩ := B.uses_inserted_edge hfree
  have hleftT : B.core (broomLeft a i)∈T := by
    simpa only [hi] using B.left_mem i
  have hleftc : B.core (broomLeft a i)=c :=
    high_T _ hleftT (inserted_edge_left_degree ha B i)
  have hcm : B.core 0∈(B.edge 0).val := by
    simpa [broomLeft] using B.left_mem 0
  have hbm : B.core (stemVertex a)∈(B.edge 0).val := by
    simpa [broomRight,stemVertex] using B.right_mem 0
  have hmidne : (B.edge 0).val≠T := by
    intro h
    have hcc : B.core 0=c := high_T _ (by simpa only [h] using hcm)
      (ha.trans B.center_degree_le)
    have hbc : B.core (stemVertex a)=c :=
      high_T _ (by simpa only [h] using hbm) (B.stem_degree_le (by omega))
    exact B.center_ne_stem (hcc.trans hbc.symm)
  have hmid : (B.edge 0).val∈E :=
    (Finset.mem_insert.mp (B.edge 0).property).resolve_left hmidne
  by_cases hii : i.val=1
  · have hbc : B.core (stemVertex a)=c := by
      simpa [broomLeft,hii,stemVertex] using hleftc
    have hne : B.core 0≠c := by simpa [hbc] using B.center_ne_stem
    have hcMid : c∈(B.edge 0).val := hbc ▸ hbm
    have hbound := neighbor_after _ hmid hcMid _ hcm hne
    have hdegree := B.center_degree_le
    omega
  · have hcc : B.core 0=c := by simpa [broomLeft,hii] using hleftc
    have hne : B.core (stemVertex a)≠c := by
      simpa [hcc] using B.center_ne_stem.symm
    have hcMid : c∈(B.edge 0).val := hcc ▸ hcm
    have hbound := neighbor_after _ hmid hcMid _ hbm hne
    have hdegree := B.stem_degree_le (by omega)
    omega

theorem saturated_looseRoot_isolates_card {a r : ℕ} (ha : 3≤a) (hr : 3≤r)
    (H : UniformHypergraph V r) (hSat : Saturated a H) (c : V)
    (hd : 2≤degree H.edges c)
    (hc : ∀e∈H.edges,c∈e→∀v∈e,v≠c→degree H.edges v≤1) :
    (isolatedVertices H.edges).card≤r-2 := by
  classical
  by_contra hn
  have hlarge : r-1≤(isolatedVertices H.edges).card := by omega
  obtain ⟨Z,hsub,hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hzero (v : V) (hv : v∈Z) : degree H.edges v=0 :=
    mem_isolatedVertices.mp (hsub hv)
  have hcZ : c∉Z := by
    intro h
    have hz := hzero c h
    omega
  let T := insert c Z
  have hTcard : T.card=r := by
    simp only [T,Finset.card_insert_of_notMem hcZ,hcard]
    omega
  have hmissing : T∉H.edges := by
    intro hmem
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<Z.card by omega)
    exact zero_degree_not_mem (hzero v hv) hmem (Finset.mem_insert_of_mem hv)
  have hfree := free_insert_at_looseRoot (by omega) hSat.1 c T
    (by
      intro v hv
      rcases Finset.mem_insert.mp hv with h | h
      · exact Or.inl h
      · exact Or.inr (hzero v h)) hc
  exact hfree (hSat.2 T hTcard hmissing)

theorem zeroComponentCount_eq_isolates {r : ℕ} (H : UniformHypergraph V r)
    (hr : 1≤r) : zeroComponentCount H=(isolatedVertices H.edges).card := by
  exact zero_component_count hr H

theorem singleComponentCount_eq_isolatedEdges {r : ℕ} (H : UniformHypergraph V r) :
    singleComponentCount H=(isolatedEdges H.edges).card := by
  exact one_component_count H

theorem largeTree_global_looseRoot {a r : ℕ} (H : UniformHypergraph V r)
    (ha : 3≤a) (hr : 3≤r) (hSat : Saturated a H)
    (hlarge : 0<largeTreeCount H) :
    ∃ c:V, a≤degree H.edges c ∧
      ∀e∈H.edges,c∈e→∀v∈e,v≠c→degree H.edges v≤1 := by
  classical
  obtain ⟨d,hd⟩ := Finset.card_pos.mp hlarge
  obtain ⟨ht,hm⟩ := (mem_largeTreeComponents H d).mp hd
  have hdsat := componentHypergraph_saturated (by omega) H hSat d
  obtain ⟨c,hdeg,hcone,hother⟩ := saturated_tree_is_loose
    (componentHypergraph H d) ha hr hdsat ht hm
  refine ⟨c.val,?_,?_⟩
  · simpa only [componentHypergraph_degree] using hdeg
  · intro e he hce v hv hvc
    have hec : (incidenceGraph H.edges).connectedComponentMk
        (.inr (⟨e,he⟩ : {e // e∈H.edges}))=d :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (incidenceGraph H.edges).Adj (.inl c.val)
          (.inr (⟨e,he⟩ : {e // e∈H.edges})) from hce)).symm.trans c.property
    let ef : ComponentEdge H.edges d := ⟨⟨e,he⟩,hec⟩
    let vv : ComponentVertex H.edges d := ⟨v,vertex_component_of_mem H.edges d ef hv⟩
    have hne : vv≠c := by
      intro h
      exact hvc (congrArg Subtype.val h)
    have hh := hother vv hne
    simpa only [componentHypergraph_degree] using hh

theorem saturated_largeTree_isolates_card {a r : ℕ} (H : UniformHypergraph V r)
    (ha : 3≤a) (hr : 3≤r) (hSat : Saturated a H)
    (hlarge : 0<largeTreeCount H) : zeroComponentCount H≤r-2 := by
  obtain ⟨c,hc,hroot⟩ := largeTree_global_looseRoot H ha hr hSat hlarge
  rw [zeroComponentCount_eq_isolates H (by omega)]
  exact saturated_looseRoot_isolates_card ha hr H hSat c (by omega) hroot

theorem saturated_exceptional_component_budgets {a r : ℕ}
    (H : UniformHypergraph V r) (ha : 3≤a) (hr : 3≤r) (hSat : Saturated a H) :
    singleComponentCount H≤1 ∧ zeroComponentCount H≤r-1 ∧
      (singleComponentCount H=0 ∨ zeroComponentCount H=0) ∧
      (0<largeTreeCount H → zeroComponentCount H≤r-2) := by
  refine ⟨?_,?_,?_,saturated_largeTree_isolates_card H ha hr hSat⟩
  · rw [singleComponentCount_eq_isolatedEdges]
    exact saturated_isolatedEdges_card ha hr H hSat
  · rw [zeroComponentCount_eq_isolates H (by omega)]
    exact saturated_isolatedVertices_card ha hr H hSat
  · by_cases he : singleComponentCount H=0
    · exact Or.inl he
    · right
      have hp : 0<(isolatedEdges H.edges).card := by
        rw [←singleComponentCount_eq_isolatedEdges]
        omega
      obtain ⟨e,he⟩ := Finset.card_pos.mp hp
      rw [zeroComponentCount_eq_isolates H (by omega),
        saturated_isolatedEdge_no_isolates ha hr H hSat he]
      rfl

end Berge
