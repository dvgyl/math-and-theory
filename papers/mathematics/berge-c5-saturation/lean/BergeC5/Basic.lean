import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Berge five-cycles and Berge-C₅ saturation of three-uniform hypergraphs

A hypergraph on a vertex type `V` is a finite set `H : Finset (Finset V)` of hyperedges.
A *Berge-C₅* in `H` consists of five distinct vertices `v₀, …, v₄` and five distinct
hyperedges `e₀, …, e₄` of `H` with `{vᵢ, vᵢ₊₁} ⊆ eᵢ`, indices modulo five.  Hyperedges may
contain further cycle vertices; no linearity or inducedness condition is imposed.

A three-uniform hypergraph is *Berge-C₅-saturated* when it contains no Berge-C₅ but adding any
absent three-element vertex set creates one.  The added set is arbitrary: it may meet existing
hyperedges in two vertices.  The saturation number `sat₃(n, Berge-C₅)` is the least number of
hyperedges of such a hypergraph on the vertex set `Fin n`; isolated vertices are allowed.
-/

namespace BergeC5

variable {V W : Type*}

/-- `v` and `e` form a Berge-`C₅` in `H`: five distinct vertices, five distinct hyperedges of
`H`, and `{v i, v (i + 1)} ⊆ e i` for every `i : Fin 5` (so `v 4, v 0 ∈ e 4`). -/
structure IsBergeC5 (H : Finset (Finset V)) (v : Fin 5 → V) (e : Fin 5 → Finset V) : Prop where
  vertices_injective : Function.Injective v
  edges_injective : Function.Injective e
  edges_mem : ∀ i, e i ∈ H
  left_mem : ∀ i, v i ∈ e i
  right_mem : ∀ i, v (i + 1) ∈ e i

/-- `H` contains a Berge copy of the five-cycle. -/
def ContainsBergeC5 (H : Finset (Finset V)) : Prop :=
  ∃ v e, IsBergeC5 H v e

/-- Every hyperedge has exactly three vertices. -/
def IsThreeUniform (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- `H` is a three-uniform Berge-`C₅`-saturated hypergraph: it is three-uniform, contains no
Berge-`C₅`, and adding any absent three-element vertex set creates a Berge-`C₅`. -/
def IsBergeC5Saturated [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  IsThreeUniform H ∧ ¬ ContainsBergeC5 H ∧
    ∀ f : Finset V, f.card = 3 → f ∉ H → ContainsBergeC5 (insert f H)

/-- `sat₃(n, Berge-C₅)`: the least number of hyperedges of a three-uniform Berge-`C₅`-saturated
hypergraph on the vertex set `Fin n`. -/
noncomputable def satNumber (n : ℕ) : ℕ :=
  sInf {k | ∃ H : Finset (Finset (Fin n)), IsBergeC5Saturated H ∧ H.card = k}

theorem satNumber_le {n : ℕ} {H : Finset (Finset (Fin n))} (h : IsBergeC5Saturated H) :
    satNumber n ≤ H.card :=
  Nat.sInf_le ⟨H, h, rfl⟩

/-- The saturation number equals `k` when some saturated hypergraph has `k` hyperedges and
every saturated hypergraph has at least `k`. -/
theorem satNumber_eq {n k : ℕ} {H : Finset (Finset (Fin n))} (h : IsBergeC5Saturated H)
    (hk : H.card = k) (hlow : ∀ H' : Finset (Finset (Fin n)), IsBergeC5Saturated H' → k ≤ H'.card) :
    satNumber n = k := by
  refine le_antisymm (hk ▸ satNumber_le h) ?_
  obtain ⟨H', h', hc⟩ := Nat.sInf_mem (s := {k | ∃ H : Finset (Finset (Fin n)),
    IsBergeC5Saturated H ∧ H.card = k}) ⟨k, H, h, hk⟩
  unfold satNumber
  rw [← hc]
  exact hlow H' h'

/-! ## Four-edge Berge paths -/

/-- A Berge path with four hyperedges from `a` to `b`: distinct vertices `a, p, q, s, b` and
distinct hyperedges `e₁, e₂, e₃, e₄` of `H` with `{a, p} ⊆ e₁`, `{p, q} ⊆ e₂`, `{q, s} ⊆ e₃`
and `{s, b} ⊆ e₄`. -/
def Path4 (H : Finset (Finset V)) (a b : V) : Prop :=
  ∃ p q s : V, ∃ e₁ e₂ e₃ e₄ : Finset V, e₁ ∈ H ∧ e₂ ∈ H ∧ e₃ ∈ H ∧ e₄ ∈ H ∧
    e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₁ ≠ e₄ ∧ e₂ ≠ e₃ ∧ e₂ ≠ e₄ ∧ e₃ ≠ e₄ ∧
    a ≠ p ∧ a ≠ q ∧ a ≠ s ∧ a ≠ b ∧ p ≠ q ∧ p ≠ s ∧ p ≠ b ∧ q ≠ s ∧ q ≠ b ∧ s ≠ b ∧
    a ∈ e₁ ∧ p ∈ e₁ ∧ p ∈ e₂ ∧ q ∈ e₂ ∧ q ∈ e₃ ∧ s ∈ e₃ ∧ s ∈ e₄ ∧ b ∈ e₄

theorem Path4.symm {H : Finset (Finset V)} {a b : V} (h : Path4 H a b) : Path4 H b a := by
  obtain ⟨p, q, s, e₁, e₂, e₃, e₄, h₁, h₂, h₃, h₄, h12, h13, h14, h23, h24, h34,
    hap, haq, has, hab, hpq, hps, hpb, hqs, hqb, hsb,
    ha1, hp1, hp2, hq2, hq3, hs3, hs4, hb4⟩ := h
  exact ⟨s, q, p, e₄, e₃, e₂, e₁, h₄, h₃, h₂, h₁, h34.symm, h24.symm, h14.symm, h23.symm,
    h13.symm, h12.symm, hsb.symm, hqb.symm, hpb.symm, hab.symm, hqs.symm, hps.symm, has.symm,
    hpq.symm, haq.symm, hap.symm, hb4, hs4, hs3, hq3, hq2, hp2, hp1, ha1⟩

/-- Every hypergraph obtained by adding a new set containing both ends of a four-edge Berge
path contains a Berge-`C₅`. -/
theorem containsBergeC5_insert_of_path4 [DecidableEq V] {H : Finset (Finset V)} {a b : V}
    {f : Finset V} (h : Path4 H a b) (hf : f ∉ H) (ha : a ∈ f) (hb : b ∈ f) :
    ContainsBergeC5 (insert f H) := by
  obtain ⟨p, q, s, e₁, e₂, e₃, e₄, h₁, h₂, h₃, h₄, h12, h13, h14, h23, h24, h34,
    hap, haq, has, hab, hpq, hps, hpb, hqs, hqb, hsb,
    ha1, hp1, hp2, hq2, hq3, hs3, hs4, hb4⟩ := h
  have h1f : e₁ ≠ f := fun h => hf (h ▸ h₁)
  have h2f : e₂ ≠ f := fun h => hf (h ▸ h₂)
  have h3f : e₃ ≠ f := fun h => hf (h ▸ h₃)
  have h4f : e₄ ≠ f := fun h => hf (h ▸ h₄)
  refine ⟨![a, p, q, s, b], ![e₁, e₂, e₃, e₄, f], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i
    fin_cases i <;> simp [h₁, h₂, h₃, h₄]
  · intro i
    fin_cases i <;> simp [ha1, hp2, hq3, hs4, hb]
  · intro i
    fin_cases i <;> simp [hp1, hq2, hs3, hb4, ha]

/-- Paths in a hypergraph remain paths in any larger hypergraph. -/
theorem Path4.mono {H H' : Finset (Finset V)} (hHH' : H ⊆ H') {a b : V} (h : Path4 H a b) :
    Path4 H' a b := by
  obtain ⟨p, q, s, e₁, e₂, e₃, e₄, h₁, h₂, h₃, h₄, rest⟩ := h
  exact ⟨p, q, s, e₁, e₂, e₃, e₄, hHH' h₁, hHH' h₂, hHH' h₃, hHH' h₄, rest⟩

/-! ## Images of hypergraphs under injective vertex maps -/

/-- The image of a hypergraph under an injective map of vertices. -/
def mapHyp (g : V ↪ W) (H : Finset (Finset V)) : Finset (Finset W) :=
  H.map ⟨Finset.map g, Finset.map_injective g⟩

theorem mem_mapHyp {g : V ↪ W} {H : Finset (Finset V)} {s : Finset V} :
    s.map g ∈ mapHyp g H ↔ s ∈ H := by
  simp [mapHyp]

theorem card_mapHyp (g : V ↪ W) (H : Finset (Finset V)) : (mapHyp g H).card = H.card :=
  Finset.card_map _

theorem isThreeUniform_mapHyp {g : V ↪ W} {B : Finset (Finset V)} (hB : IsThreeUniform B) :
    IsThreeUniform (mapHyp g B) := by
  intro e he
  obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 he
  simpa using hB s hs

theorem Path4.map {g : V ↪ W} {H : Finset (Finset V)} {H' : Finset (Finset W)}
    (hH : mapHyp g H ⊆ H') {a b : V} (h : Path4 H a b) : Path4 H' (g a) (g b) := by
  obtain ⟨p, q, s, e₁, e₂, e₃, e₄, h₁, h₂, h₃, h₄, h12, h13, h14, h23, h24, h34,
    hap, haq, has, hab, hpq, hps, hpb, hqs, hqb, hsb,
    ha1, hp1, hp2, hq2, hq3, hs3, hs4, hb4⟩ := h
  have hm : ∀ e ∈ H, e.map g ∈ H' := fun e he => hH (mem_mapHyp.2 he)
  have hne : ∀ {e e' : Finset V}, e ≠ e' → e.map g ≠ e'.map g :=
    fun h h' => h (Finset.map_injective g h')
  have hv : ∀ {x y : V}, x ≠ y → g x ≠ g y := fun h => g.injective.ne h
  exact ⟨g p, g q, g s, e₁.map g, e₂.map g, e₃.map g, e₄.map g, hm _ h₁, hm _ h₂, hm _ h₃,
    hm _ h₄, hne h12, hne h13, hne h14, hne h23, hne h24, hne h34, hv hap, hv haq, hv has,
    hv hab, hv hpq, hv hps, hv hpb, hv hqs, hv hqb, hv hsb, Finset.mem_map_of_mem g ha1,
    Finset.mem_map_of_mem g hp1, Finset.mem_map_of_mem g hp2, Finset.mem_map_of_mem g hq2,
    Finset.mem_map_of_mem g hq3, Finset.mem_map_of_mem g hs3, Finset.mem_map_of_mem g hs4,
    Finset.mem_map_of_mem g hb4⟩

/-- A Berge-`C₅` in the image of a hypergraph under an injective vertex map comes from a
Berge-`C₅` of the hypergraph. -/
theorem ContainsBergeC5.of_mapHyp {g : V ↪ W} {H : Finset (Finset V)}
    (h : ContainsBergeC5 (mapHyp g H)) : ContainsBergeC5 H := by
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

theorem ContainsBergeC5.relabel (e : V ≃ W) {H : Finset (Finset V)} (h : ContainsBergeC5 H) :
    ContainsBergeC5 (relabel e H) := by
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
theorem IsBergeC5Saturated.relabel [DecidableEq V] [DecidableEq W] (e : V ≃ W)
    {H : Finset (Finset V)} (h : IsBergeC5Saturated H) : IsBergeC5Saturated (relabel e H) := by
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
    have heq : BergeC5.relabel e (insert (f.map e.symm.toEmbedding) H) =
        insert f (BergeC5.relabel e H) := by
      simp only [BergeC5.relabel, mapHyp, Finset.map_insert, Function.Embedding.coeFn_mk,
        map_map_symm]
    rwa [heq] at hc

/-! ## Elementary consequences -/

/-- A Berge-`C₅` uses five distinct hyperedges. -/
theorem ContainsBergeC5.five_le_card {H : Finset (Finset V)} (h : ContainsBergeC5 H) :
    5 ≤ H.card := by
  classical
  obtain ⟨v, e, hc⟩ := h
  have hsub : Finset.univ.image e ⊆ H := by
    intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    exact hc.edges_mem i
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hc.edges_injective, Finset.card_univ,
    Fintype.card_fin] at this

/-- A Berge-`C₅` uses five distinct vertices. -/
theorem ContainsBergeC5.five_le_card_vertices [Fintype V] {H : Finset (Finset V)}
    (h : ContainsBergeC5 H) : 5 ≤ Fintype.card V := by
  obtain ⟨v, e, hc⟩ := h
  simpa using Fintype.card_le_of_injective v hc.vertices_injective

theorem not_containsBergeC5_of_card_lt {H : Finset (Finset V)} (h : H.card < 5) :
    ¬ ContainsBergeC5 H :=
  fun hc => by have := hc.five_le_card; omega

/-- Every saturated hypergraph on at least `k` vertices with `k ≤ 4` has at least
`k.choose 3` hyperedges when `k = 3` and at least four when `k ≥ 4`: an absent triple would have
to complete a Berge-`C₅` with at most four further hyperedges. -/
theorem card_ge_of_saturated [Fintype V] [DecidableEq V] {H : Finset (Finset V)} {k : ℕ}
    (hk : k ≤ 4) (hV : k ≤ Fintype.card V) (h : IsBergeC5Saturated H) : k.choose 3 ≤ H.card := by
  by_contra hlt
  rw [not_le] at hlt
  have hcard : H.card < (Finset.univ.powersetCard 3 : Finset (Finset V)).card := by
    rw [Finset.card_powersetCard, Finset.card_univ]
    exact lt_of_lt_of_le hlt (Nat.choose_le_choose 3 hV)
  obtain ⟨f, hf, hfH⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hf3 : f.card = 3 := (Finset.mem_powersetCard.1 hf).2
  have hc := h.2.2 f hf3 hfH
  have := hc.five_le_card
  have := Finset.card_insert_le f H
  have : k.choose 3 ≤ 4 := by interval_cases k <;> decide
  omega

/-! ## Saturation from four-edge paths -/

/-- Every absent three-element set contains the two ends of a four-edge Berge path. -/
def PathSaturated (H : Finset (Finset V)) : Prop :=
  ∀ f : Finset V, f.card = 3 → f ∉ H → ∃ a ∈ f, ∃ b ∈ f, Path4 H a b

theorem isBergeC5Saturated_of_pathSaturated [DecidableEq V] {H : Finset (Finset V)}
    (hu : IsThreeUniform H) (hfree : ¬ ContainsBergeC5 H) (hsat : PathSaturated H) :
    IsBergeC5Saturated H := by
  refine ⟨hu, hfree, fun f hf hfH => ?_⟩
  obtain ⟨a, ha, b, hb, hp⟩ := hsat f hf hfH
  exact containsBergeC5_insert_of_path4 hp hfH ha hb

/-- An absent triple inside the image of a path-saturated hypergraph contains the ends of a
four-edge path. -/
theorem path_of_sub [Fintype V] [DecidableEq V] {g : V ↪ W}
    {B : Finset (Finset V)} {H : Finset (Finset W)} (hBH : mapHyp g B ⊆ H) (hB : PathSaturated B)
    {f : Finset W} (hf : f.card = 3) (hfH : f ∉ H) (hrange : ∀ x ∈ f, ∃ y, g y = x) :
    ∃ a ∈ f, ∃ b ∈ f, Path4 H a b := by
  classical
  set f' := Finset.univ.filter (fun y => g y ∈ f) with hf'def
  have hmap : f'.map g = f := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
      simpa [f'] using hy
    · intro hx
      obtain ⟨y, rfl⟩ := hrange x hx
      exact Finset.mem_map_of_mem g (by simpa [f'] using hx)
  have hf' : f'.card = 3 := by rw [← hf, ← hmap, Finset.card_map]
  have hf'B : f' ∉ B := fun h => hfH (hmap ▸ hBH (mem_mapHyp.2 h))
  obtain ⟨a, ha, b, hb, hp⟩ := hB f' hf' hf'B
  exact ⟨g a, hmap ▸ Finset.mem_map_of_mem g ha, g b, hmap ▸ Finset.mem_map_of_mem g hb,
    hp.map hBH⟩

end BergeC5
