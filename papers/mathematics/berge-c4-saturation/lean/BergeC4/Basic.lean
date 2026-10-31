import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Berge four-cycles and Berge-C₄ saturation of three-uniform hypergraphs

A hypergraph on a vertex type `V` is a finite set `H : Finset (Finset V)` of hyperedges.
A *Berge-C₄* in `H` consists of four distinct vertices `v₀, v₁, v₂, v₃` and four distinct
hyperedges `e₀, e₁, e₂, e₃` of `H` with `{vᵢ, vᵢ₊₁} ⊆ eᵢ`, indices modulo four.  Hyperedges may
contain further cycle vertices; no linearity or inducedness condition is imposed.

A three-uniform hypergraph is *Berge-C₄-saturated* when it contains no Berge-C₄ but adding any
absent three-element vertex set creates one.  The added set is arbitrary: it may meet existing
hyperedges in two vertices.  The saturation number `sat₃(n, Berge-C₄)` is the least number of
hyperedges of such a hypergraph on the vertex set `Fin n`; isolated vertices are allowed.
-/

namespace BergeC4

variable {V W : Type*}

/-- `v` and `e` form a Berge-`C₄` in `H`: four distinct vertices, four distinct hyperedges of
`H`, and `{v i, v (i + 1)} ⊆ e i` for every `i : Fin 4` (so `v 3, v 0 ∈ e 3`). -/
structure IsBergeC4 (H : Finset (Finset V)) (v : Fin 4 → V) (e : Fin 4 → Finset V) : Prop where
  vertices_injective : Function.Injective v
  edges_injective : Function.Injective e
  edges_mem : ∀ i, e i ∈ H
  left_mem : ∀ i, v i ∈ e i
  right_mem : ∀ i, v (i + 1) ∈ e i

/-- `H` contains a Berge copy of the four-cycle. -/
def ContainsBergeC4 (H : Finset (Finset V)) : Prop :=
  ∃ v e, IsBergeC4 H v e

/-- Every hyperedge has exactly three vertices. -/
def IsThreeUniform (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- `H` is a three-uniform Berge-`C₄`-saturated hypergraph: it is three-uniform, contains no
Berge-`C₄`, and adding any absent three-element vertex set creates a Berge-`C₄`. -/
def IsBergeC4Saturated [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  IsThreeUniform H ∧ ¬ ContainsBergeC4 H ∧
    ∀ f : Finset V, f.card = 3 → f ∉ H → ContainsBergeC4 (insert f H)

/-- `sat₃(n, Berge-C₄)`: the least number of hyperedges of a three-uniform Berge-`C₄`-saturated
hypergraph on the vertex set `Fin n`. -/
noncomputable def satNumber (n : ℕ) : ℕ :=
  sInf {k | ∃ H : Finset (Finset (Fin n)), IsBergeC4Saturated H ∧ H.card = k}

theorem satNumber_le {n : ℕ} {H : Finset (Finset (Fin n))} (h : IsBergeC4Saturated H) :
    satNumber n ≤ H.card :=
  Nat.sInf_le ⟨H, h, rfl⟩

/-- The saturation number equals `k` when some saturated hypergraph has `k` hyperedges and
every saturated hypergraph has at least `k`. -/
theorem satNumber_eq {n k : ℕ} {H : Finset (Finset (Fin n))} (h : IsBergeC4Saturated H)
    (hk : H.card = k) (hlow : ∀ H' : Finset (Finset (Fin n)), IsBergeC4Saturated H' → k ≤ H'.card) :
    satNumber n = k := by
  refine le_antisymm (hk ▸ satNumber_le h) ?_
  obtain ⟨H', h', hc⟩ := Nat.sInf_mem (s := {k | ∃ H : Finset (Finset (Fin n)),
    IsBergeC4Saturated H ∧ H.card = k}) ⟨k, H, h, hk⟩
  unfold satNumber
  rw [← hc]
  exact hlow H' h'

/-! ## Three-edge Berge paths -/

/-- A Berge path with three hyperedges from `a` to `b`: distinct vertices `a, p, q, b` and
distinct hyperedges `e₁, e₂, e₃` of `H` with `{a, p} ⊆ e₁`, `{p, q} ⊆ e₂`, `{q, b} ⊆ e₃`. -/
def Path3 (H : Finset (Finset V)) (a b : V) : Prop :=
  ∃ p q : V, ∃ e₁ e₂ e₃ : Finset V, e₁ ∈ H ∧ e₂ ∈ H ∧ e₃ ∈ H ∧ e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
    a ≠ p ∧ a ≠ q ∧ a ≠ b ∧ p ≠ q ∧ p ≠ b ∧ q ≠ b ∧
    a ∈ e₁ ∧ p ∈ e₁ ∧ p ∈ e₂ ∧ q ∈ e₂ ∧ q ∈ e₃ ∧ b ∈ e₃

theorem Path3.symm {H : Finset (Finset V)} {a b : V} (h : Path3 H a b) : Path3 H b a := by
  obtain ⟨p, q, e₁, e₂, e₃, h₁, h₂, h₃, h12, h13, h23, hap, haq, hab, hpq, hpb, hqb,
    ha1, hp1, hp2, hq2, hq3, hb3⟩ := h
  exact ⟨q, p, e₃, e₂, e₁, h₃, h₂, h₁, h23.symm, h13.symm, h12.symm, hqb.symm, hpb.symm,
    hab.symm, hpq.symm, haq.symm, hap.symm, hb3, hq3, hq2, hp2, hp1, ha1⟩

/-- Every hypergraph obtained by adding a new set containing both ends of a three-edge Berge
path contains a Berge-`C₄`. -/
theorem containsBergeC4_insert_of_path3 [DecidableEq V] {H : Finset (Finset V)} {a b : V} {f : Finset V}
    (h : Path3 H a b) (hf : f ∉ H) (ha : a ∈ f) (hb : b ∈ f) :
    ContainsBergeC4 (insert f H) := by
  obtain ⟨p, q, e₁, e₂, e₃, h₁, h₂, h₃, h12, h13, h23, hap, haq, hab, hpq, hpb, hqb,
    ha1, hp1, hp2, hq2, hq3, hb3⟩ := h
  have h1f : e₁ ≠ f := fun h => hf (h ▸ h₁)
  have h2f : e₂ ≠ f := fun h => hf (h ▸ h₂)
  have h3f : e₃ ≠ f := fun h => hf (h ▸ h₃)
  refine ⟨![a, p, q, b], ![e₁, e₂, e₃, f], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i
    fin_cases i <;> simp [h₁, h₂, h₃]
  · intro i
    fin_cases i <;> simp [ha1, hp2, hq3, hb]
  · intro i
    fin_cases i <;> simp [hp1, hq2, hb3, ha]

/-- Paths in a hypergraph remain paths in any larger hypergraph. -/
theorem Path3.mono {H H' : Finset (Finset V)} (hHH' : H ⊆ H') {a b : V} (h : Path3 H a b) :
    Path3 H' a b := by
  obtain ⟨p, q, e₁, e₂, e₃, h₁, h₂, h₃, rest⟩ := h
  exact ⟨p, q, e₁, e₂, e₃, hHH' h₁, hHH' h₂, hHH' h₃, rest⟩

/-! ## Images of hypergraphs under injective vertex maps -/

/-- The image of a hypergraph under an injective map of vertices. -/
def mapHyp (g : V ↪ W) (H : Finset (Finset V)) : Finset (Finset W) :=
  H.map ⟨Finset.map g, Finset.map_injective g⟩

theorem mem_mapHyp {g : V ↪ W} {H : Finset (Finset V)} {s : Finset V} :
    s.map g ∈ mapHyp g H ↔ s ∈ H := by
  simp [mapHyp]

theorem card_mapHyp (g : V ↪ W) (H : Finset (Finset V)) : (mapHyp g H).card = H.card :=
  Finset.card_map _

theorem Path3.map {g : V ↪ W} {H : Finset (Finset V)} {H' : Finset (Finset W)}
    (hH : mapHyp g H ⊆ H') {a b : V} (h : Path3 H a b) : Path3 H' (g a) (g b) := by
  obtain ⟨p, q, e₁, e₂, e₃, h₁, h₂, h₃, h12, h13, h23, hap, haq, hab, hpq, hpb, hqb,
    ha1, hp1, hp2, hq2, hq3, hb3⟩ := h
  have hm : ∀ e ∈ H, e.map g ∈ H' := fun e he => hH (mem_mapHyp.2 he)
  have hne : ∀ {e e' : Finset V}, e ≠ e' → e.map g ≠ e'.map g :=
    fun h h' => h (Finset.map_injective g h')
  exact ⟨g p, g q, e₁.map g, e₂.map g, e₃.map g, hm _ h₁, hm _ h₂, hm _ h₃, hne h12, hne h13,
    hne h23, g.injective.ne hap, g.injective.ne haq, g.injective.ne hab, g.injective.ne hpq,
    g.injective.ne hpb, g.injective.ne hqb, Finset.mem_map_of_mem g ha1,
    Finset.mem_map_of_mem g hp1, Finset.mem_map_of_mem g hp2, Finset.mem_map_of_mem g hq2,
    Finset.mem_map_of_mem g hq3, Finset.mem_map_of_mem g hb3⟩

/-- A Berge-`C₄` in the image of a hypergraph under an injective vertex map comes from a
Berge-`C₄` of the hypergraph. -/
theorem ContainsBergeC4.of_mapHyp {g : V ↪ W} {H : Finset (Finset V)}
    (h : ContainsBergeC4 (mapHyp g H)) : ContainsBergeC4 H := by
  classical
  obtain ⟨v, e, hc⟩ := h
  have he : ∀ i, ∃ s ∈ H, s.map g = e i := fun i => by
    have := hc.edges_mem i
    simpa [mapHyp] using this
  choose s hsH hs using he
  have hv : ∀ i, ∃ x, g x = v i := fun i => by
    have := hc.left_mem i
    rw [← hs i] at this
    obtain ⟨x, -, hx⟩ := Finset.mem_map.1 this
    exact ⟨x, hx⟩
  choose w hw using hv
  refine ⟨w, s, ⟨?_, ?_, hsH, ?_, ?_⟩⟩
  · intro i j hij
    apply hc.vertices_injective
    rw [← hw i, ← hw j, hij]
  · intro i j hij
    apply hc.edges_injective
    rw [← hs i, ← hs j, hij]
  · intro i
    have := hc.left_mem i
    rw [← hs i, ← hw i] at this
    exact (Finset.mem_map' g).1 this
  · intro i
    have := hc.right_mem i
    rw [← hs i, ← hw (i + 1)] at this
    exact (Finset.mem_map' g).1 this

/-! ## Relabelling -/

/-- Relabel the vertices of every hyperedge along an equivalence. -/
def relabel (e : V ≃ W) (H : Finset (Finset V)) : Finset (Finset W) :=
  mapHyp e.toEmbedding H

theorem map_symm_map (e : V ≃ W) (s : Finset V) :
    (s.map e.toEmbedding).map e.symm.toEmbedding = s := by
  ext x
  simp

theorem map_map_symm (e : V ≃ W) (s : Finset W) :
    (s.map e.symm.toEmbedding).map e.toEmbedding = s := by
  ext x
  simp

theorem mem_relabel {e : V ≃ W} {H : Finset (Finset V)} {s : Finset W} :
    s ∈ relabel e H ↔ s.map e.symm.toEmbedding ∈ H := by
  constructor
  · intro hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 hs
    simpa [map_symm_map] using hs'
  · intro hs
    exact Finset.mem_map.2 ⟨_, hs, map_map_symm e s⟩

theorem card_relabel (e : V ≃ W) (H : Finset (Finset V)) : (relabel e H).card = H.card :=
  Finset.card_map _

theorem relabel_symm_relabel (e : V ≃ W) (H : Finset (Finset V)) :
    relabel e.symm (relabel e H) = H := by
  ext s
  rw [mem_relabel, mem_relabel, Equiv.symm_symm, map_symm_map]

theorem ContainsBergeC4.relabel (e : V ≃ W) {H : Finset (Finset V)} (h : ContainsBergeC4 H) :
    ContainsBergeC4 (relabel e H) := by
  obtain ⟨v, s, hc⟩ := h
  refine ⟨fun i => e (v i), fun i => (s i).map e.toEmbedding, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact e.injective.comp hc.vertices_injective
  · exact (Finset.map_injective _).comp hc.edges_injective
  · intro i
    exact Finset.mem_map_of_mem _ (hc.edges_mem i)
  · intro i
    exact Finset.mem_map_of_mem _ (hc.left_mem i)
  · intro i
    exact Finset.mem_map_of_mem _ (hc.right_mem i)

/-- Saturation is invariant under relabelling the vertices. -/
theorem IsBergeC4Saturated.relabel [DecidableEq V] [DecidableEq W] (e : V ≃ W)
    {H : Finset (Finset V)} (h : IsBergeC4Saturated H) : IsBergeC4Saturated (relabel e H) := by
  obtain ⟨hu, hfree, hsat⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 hs
    simpa using hu s' hs'
  · intro hc
    apply hfree
    simpa [relabel_symm_relabel] using hc.relabel e.symm
  · intro f hf hfH
    have hg : (f.map e.symm.toEmbedding).card = 3 := by simpa using hf
    have hgH : f.map e.symm.toEmbedding ∉ H := fun h' => hfH (mem_relabel.2 h')
    have hc := (hsat _ hg hgH).relabel e
    have heq : BergeC4.relabel e (insert (f.map e.symm.toEmbedding) H) =
        insert f (BergeC4.relabel e H) := by
      simp only [BergeC4.relabel, mapHyp, Finset.map_insert, Function.Embedding.coeFn_mk,
        map_map_symm]
    rwa [heq] at hc

/-! ## Elementary consequences -/

/-- A Berge-`C₄` uses four distinct hyperedges. -/
theorem ContainsBergeC4.four_le_card {H : Finset (Finset V)} (h : ContainsBergeC4 H) :
    4 ≤ H.card := by
  classical
  obtain ⟨v, e, hc⟩ := h
  have hsub : Finset.univ.image e ⊆ H := by
    intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    exact hc.edges_mem i
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hc.edges_injective, Finset.card_univ,
    Fintype.card_fin] at this

theorem not_containsBergeC4_of_card_lt {H : Finset (Finset V)} (h : H.card < 4) :
    ¬ ContainsBergeC4 H :=
  fun hc => by have := hc.four_le_card; omega

/-- A hypergraph is Berge-`C₄`-free when every vertex lying in two distinct hyperedges belongs
to a set of at most three vertices: the four cycle vertices would all lie in that set. -/
theorem not_containsBergeC4_of_hubs {H : Finset (Finset V)} (S : Finset V) (hS : S.card ≤ 3)
    (hhub : ∀ x, ∀ e₁ ∈ H, ∀ e₂ ∈ H, e₁ ≠ e₂ → x ∈ e₁ → x ∈ e₂ → x ∈ S) :
    ¬ ContainsBergeC4 H := by
  classical
  rintro ⟨v, e, hc⟩
  have hvS : ∀ i, v i ∈ S := by
    intro i
    have hne : i - 1 ≠ i := by fin_cases i <;> decide
    have hr := hc.right_mem (i - 1)
    have hii : i - 1 + 1 = i := by fin_cases i <;> rfl
    rw [hii] at hr
    exact hhub (v i) (e (i - 1)) (hc.edges_mem _) (e i) (hc.edges_mem _)
      (fun h => hne (hc.edges_injective h)) hr (hc.left_mem i)
  have hsub : Finset.univ.image v ⊆ S := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hvS i
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hc.vertices_injective, Finset.card_univ,
    Fintype.card_fin] at this
  omega

/-- Every saturated hypergraph on at least four vertices has at least three hyperedges. -/
theorem three_le_card_of_saturated [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
    (hV : 4 ≤ Fintype.card V) (h : IsBergeC4Saturated H) : 3 ≤ H.card := by
  by_contra hlt
  rw [not_le] at hlt
  have hcard : H.card < (Finset.univ.powersetCard 3 : Finset (Finset V)).card := by
    rw [Finset.card_powersetCard, Finset.card_univ]
    have : Nat.choose 4 3 ≤ Nat.choose (Fintype.card V) 3 := Nat.choose_le_choose 3 hV
    simp [Nat.choose] at this
    omega
  obtain ⟨f, hf, hfH⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hf3 : f.card = 3 := (Finset.mem_powersetCard.1 hf).2
  have hc := h.2.2 f hf3 hfH
  have := hc.four_le_card
  have := Finset.card_insert_le f H
  omega

/-- Every saturated hypergraph on at least three vertices has a hyperedge. -/
theorem one_le_card_of_saturated [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
    (hV : 3 ≤ Fintype.card V) (h : IsBergeC4Saturated H) : 1 ≤ H.card := by
  by_contra hlt
  rw [not_le] at hlt
  have hcard : H.card < (Finset.univ.powersetCard 3 : Finset (Finset V)).card := by
    rw [Finset.card_powersetCard, Finset.card_univ]
    have : Nat.choose 3 3 ≤ Nat.choose (Fintype.card V) 3 := Nat.choose_le_choose 3 hV
    simp at this
    omega
  obtain ⟨f, hf, hfH⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hf3 : f.card = 3 := (Finset.mem_powersetCard.1 hf).2
  have hc := h.2.2 f hf3 hfH
  have := hc.four_le_card
  have := Finset.card_insert_le f H
  omega

/-! ## Saturation from three-edge paths -/

/-- Every absent three-element set contains the two ends of a three-edge Berge path. -/
def PathSaturated (H : Finset (Finset V)) : Prop :=
  ∀ f : Finset V, f.card = 3 → f ∉ H → ∃ a ∈ f, ∃ b ∈ f, Path3 H a b

theorem isBergeC4Saturated_of_pathSaturated [DecidableEq V] {H : Finset (Finset V)}
    (hu : IsThreeUniform H) (hfree : ¬ ContainsBergeC4 H) (hsat : PathSaturated H) :
    IsBergeC4Saturated H := by
  refine ⟨hu, hfree, fun f hf hfH => ?_⟩
  obtain ⟨a, ha, b, hb, hp⟩ := hsat f hf hfH
  exact containsBergeC4_insert_of_path3 hp hfH ha hb

end BergeC4
