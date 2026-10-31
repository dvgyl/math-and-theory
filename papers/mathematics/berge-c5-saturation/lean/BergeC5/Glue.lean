import BergeC5.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin

/-!
# Gluing rooted saturated pieces at a common root

A *rooted piece* is a three-uniform hypergraph `H` with a root `r` such that `H` contains no
Berge-`C₅`, every absent triple contains the two ends of a four-edge Berge path, and every vertex
other than `r` is joined to `r` by a two-edge Berge path.  Two rooted pieces glued at their roots
form a rooted piece again: a Berge-`C₅` cannot pass through the cut vertex, and two non-root
vertices from different pieces are joined by a four-edge path made of their two-edge paths to the
root.  The sizes add up, which gives a semigroup of realizable pairs (non-root order, size).
-/

namespace BergeC5

section Generic

variable {V W P : Type*}

/-- A two-edge Berge path `u, w, r` through distinct hyperedges. -/
def Reach2 (H : Finset (Finset V)) (r u : V) : Prop :=
  ∃ w, ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ u ≠ w ∧ w ≠ r ∧ u ∈ e₁ ∧ w ∈ e₁ ∧ w ∈ e₂ ∧ r ∈ e₂

theorem Reach2.map {g : W ↪ V} {B : Finset (Finset W)} {H : Finset (Finset V)}
    (hBH : mapHyp g B ⊆ H) {r u : W} (h : Reach2 B r u) : Reach2 H (g r) (g u) := by
  obtain ⟨w, e₁, he₁, e₂, he₂, h12, huw, hwr, hu1, hw1, hw2, hr2⟩ := h
  exact ⟨g w, e₁.map g, hBH (mem_mapHyp.2 he₁), e₂.map g, hBH (mem_mapHyp.2 he₂),
    fun h => h12 (Finset.map_injective g h), g.injective.ne huw, g.injective.ne hwr,
    Finset.mem_map_of_mem g hu1, Finset.mem_map_of_mem g hw1, Finset.mem_map_of_mem g hw2,
    Finset.mem_map_of_mem g hr2⟩

/-- Every hyperedge has all its non-root vertices in a single piece. -/
def LocalPieces (H : Finset (Finset V)) (r : V) (π : V → P) : Prop :=
  ∀ e ∈ H, ∀ x ∈ e, ∀ y ∈ e, x ≠ r → y ≠ r → π x = π y

theorem exists_ne_of_card_eq_three {e : Finset V} (h : e.card = 3) (r : V) : ∃ x ∈ e, x ≠ r :=
  Finset.exists_mem_ne (by omega) r

/-- A Berge-`C₅` of a hypergraph with local pieces has all its non-root vertices in one piece. -/
theorem cycle_in_piece {H : Finset (Finset V)} {r : V} {π : V → P}
    (hu : IsThreeUniform H) (hloc : LocalPieces H r π) {v : Fin 5 → V} {e : Fin 5 → Finset V}
    (hc : IsBergeC5 H v e) : ∃ p, ∀ i, ∀ x ∈ e i, x ≠ r → π x = p := by
  have hw : ∀ i, ∃ x ∈ e i, x ≠ r := fun i =>
    exists_ne_of_card_eq_three (hu _ (hc.edges_mem i)) r
  choose w hwe hwr using hw
  have hcx : ∀ i, ∀ x ∈ e i, x ≠ r → π x = π (w i) := fun i x hx hxr =>
    hloc _ (hc.edges_mem i) x hx (w i) (hwe i) hxr (hwr i)
  have hlink : ∀ i, v (i + 1) ≠ r → π (w i) = π (w (i + 1)) := fun i h => by
    rw [← hcx i _ (hc.right_mem i) h, hcx (i + 1) _ (hc.left_mem (i + 1)) h]
  have hne : ∀ i j, i ≠ j → v i = r → v j ≠ r := fun i j hij hi hj =>
    hij (hc.vertices_injective (hi.trans hj.symm))
  have l0 : v 1 ≠ r → π (w 0) = π (w 1) := hlink 0
  have l1 : v 2 ≠ r → π (w 1) = π (w 2) := hlink 1
  have l2 : v 3 ≠ r → π (w 2) = π (w 3) := hlink 2
  have l3 : v 4 ≠ r → π (w 3) = π (w 4) := hlink 3
  have l4 : v 0 ≠ r → π (w 4) = π (w 0) := hlink 4
  have hall : π (w 1) = π (w 0) ∧ π (w 2) = π (w 0) ∧ π (w 3) = π (w 0) ∧
      π (w 4) = π (w 0) := by
    by_cases h0 : v 0 = r
    · have a := l0 (hne 0 1 (by decide) h0)
      have b := l1 (hne 0 2 (by decide) h0)
      have c := l2 (hne 0 3 (by decide) h0)
      have d := l3 (hne 0 4 (by decide) h0)
      exact ⟨a.symm, (a.trans b).symm, (a.trans (b.trans c)).symm,
        (a.trans (b.trans (c.trans d))).symm⟩
    · have d4 := l4 h0
      by_cases h1 : v 1 = r
      · have b := l1 (hne 1 2 (by decide) h1)
        have c := l2 (hne 1 3 (by decide) h1)
        have d := l3 (hne 1 4 (by decide) h1)
        exact ⟨b.trans (c.trans (d.trans d4)), c.trans (d.trans d4), d.trans d4, d4⟩
      · have a := l0 h1
        by_cases h2 : v 2 = r
        · have c := l2 (hne 2 3 (by decide) h2)
          have d := l3 (hne 2 4 (by decide) h2)
          exact ⟨a.symm, c.trans (d.trans d4), d.trans d4, d4⟩
        · have b := l1 h2
          by_cases h3 : v 3 = r
          · have d := l3 (hne 3 4 (by decide) h3)
            exact ⟨a.symm, (a.trans b).symm, d.trans d4, d4⟩
          · have c := l2 h3
            exact ⟨a.symm, (a.trans b).symm, (a.trans (b.trans c)).symm, d4⟩
  refine ⟨π (w 0), fun i x hx hxr => (hcx i x hx hxr).trans ?_⟩
  fin_cases i
  · rfl
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2

/-- Two-edge paths to the root from vertices of different pieces give a four-edge path between
them. -/
theorem path4_of_reach2 {H : Finset (Finset V)} {r : V} {π : V → P} (hloc : LocalPieces H r π)
    {u w : V} (hu : u ≠ r) (hw : w ≠ r) (hπ : π u ≠ π w) (h1 : Reach2 H r u)
    (h2 : Reach2 H r w) : Path4 H u w := by
  obtain ⟨p, e₁, he₁, e₂, he₂, h12, hup, hpr, hu1, hp1, hp2, hr2⟩ := h1
  obtain ⟨q, f₁, hf₁, f₂, hf₂, hf12, hwq, hqr, hw1, hq1, hq2, hr2'⟩ := h2
  have hπp : π p = π u := hloc e₁ he₁ p hp1 u hu1 hpr hu
  have hπq : π q = π w := hloc f₁ hf₁ q hq1 w hw1 hqr hw
  have hne : ∀ {x y : V}, π x = π u → π y = π w → x ≠ y := fun hx hy h =>
    hπ (by rw [← hx, ← hy, h])
  have hee : ∀ {e f : Finset V} {x y : V}, x ∈ e → y ∈ f → x ≠ r → y ≠ r → e ∈ H →
      π x = π u → π y = π w → e ≠ f := by
    intro e f x y hx hy hxr hyr he hπx hπy h
    subst h
    exact hπ (by rw [← hπx, ← hπy]; exact hloc e he x hx y hy hxr hyr)
  exact ⟨p, r, q, e₁, e₂, f₂, f₁, he₁, he₂, hf₂, hf₁, h12,
    hee hu1 hq2 hu hqr he₁ rfl hπq, hee hu1 hw1 hu hw he₁ rfl rfl,
    hee hp2 hq2 hpr hqr he₂ hπp hπq, hee hp2 hw1 hpr hw he₂ hπp rfl, hf12.symm,
    hup, hu, hne rfl hπq, hne rfl rfl, hpr, hne hπp hπq, hne hπp rfl, hqr.symm, hw.symm,
    hwq.symm, hu1, hp1, hp2, hr2, hr2', hq2, hq1, hw1⟩

end Generic

/-! ## Rooted pieces -/

section Rooted

variable {V : Type*}

/-- A rooted piece: three-uniform, Berge-`C₅`-free, path-saturated, and every non-root vertex
has a two-edge path to the root. -/
def IsRootedPiece (H : Finset (Finset V)) (r : V) : Prop :=
  IsThreeUniform H ∧ ¬ ContainsBergeC5 H ∧ PathSaturated H ∧ ∀ u, u ≠ r → Reach2 H r u

/-- `(N, k)` is realizable: some rooted piece has `N` non-root vertices and `k` hyperedges. -/
def Realizable (N k : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (r : V) (H : Finset (Finset V)),
    Fintype.card V = N + 1 ∧ IsRootedPiece H r ∧ H.card = k

/-- A rooted piece on `Fin (N + 1)` with root `0` witnesses realizability. -/
theorem realizable_of_fin {N : ℕ} {H : Finset (Finset (Fin (N + 1)))} (h : IsRootedPiece H 0) :
    Realizable N H.card :=
  ⟨Fin (N + 1), inferInstance, inferInstance, 0, H, Fintype.card_fin _, h, rfl⟩

/-- A realizable pair gives a saturated hypergraph on `Fin (N + 1)` with `k` hyperedges. -/
theorem exists_saturated_of_realizable {N k : ℕ} (h : Realizable N k) :
    ∃ H : Finset (Finset (Fin (N + 1))), IsBergeC5Saturated H ∧ H.card = k := by
  obtain ⟨V, _, _, r, H, hcard, ⟨hu, hfree, hsat, -⟩, hk⟩ := h
  let e : V ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  exact ⟨relabel e H, (isBergeC5Saturated_of_pathSaturated hu hfree hsat).relabel e,
    by rw [card_relabel, hk]⟩

/-- The one-vertex piece with no hyperedges. -/
theorem realizable_zero : Realizable 0 0 := by
  refine ⟨Fin 1, inferInstance, inferInstance, 0, ∅, Fintype.card_fin _, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
  · intro e he
    exact absurd he (Finset.notMem_empty e)
  · exact not_containsBergeC5_of_card_lt (by simp)
  · intro f hf _
    have := Finset.card_le_univ f
    simp at this
    omega
  · intro u hu
    exact absurd (Subsingleton.elim u 0) hu

end Rooted

/-! ## The gluing construction -/

section Glue

set_option linter.unusedSectionVars false

variable {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂] (r₁ : V₁) (r₂ : V₂)

/-- Glued vertices: all of `V₁`, and the non-root vertices of `V₂`. -/
abbrev GVtx := V₁ ⊕ {x : V₂ // x ≠ r₂}

/-- The first piece embeds as itself. -/
def emb₁ : V₁ ↪ GVtx (V₁ := V₁) r₂ := ⟨Sum.inl, Sum.inl_injective⟩

/-- The second piece embeds with its root sent to the root of the first. -/
def fun₂ (x : V₂) : GVtx (V₁ := V₁) r₂ :=
  if h : x = r₂ then Sum.inl r₁ else Sum.inr ⟨x, h⟩

theorem fun₂_injective : Function.Injective (fun₂ r₁ r₂) := by
  intro x y hxy
  unfold fun₂ at hxy
  by_cases hx : x = r₂ <;> by_cases hy : y = r₂
  · rw [hx, hy]
  · simp [hx, hy] at hxy
  · simp [hx, hy] at hxy
  · simp only [hx, hy, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at hxy
    exact hxy

/-- The embedding of the second piece. -/
def emb₂ : V₂ ↪ GVtx (V₁ := V₁) r₂ := ⟨fun₂ r₁ r₂, fun₂_injective r₁ r₂⟩

/-- The piece label: `true` on the first piece, `false` on the second. -/
def side : GVtx (V₁ := V₁) r₂ → Bool := Sum.isLeft

/-- The two pieces glued at their roots. -/
def glue (H₁ : Finset (Finset V₁)) (H₂ : Finset (Finset V₂)) :
    Finset (Finset (GVtx (V₁ := V₁) r₂)) :=
  mapHyp (emb₁ r₂) H₁ ∪ mapHyp (emb₂ r₁ r₂) H₂

variable {r₁ r₂}

theorem emb₂_root : emb₂ r₁ r₂ r₂ = emb₁ r₂ r₁ := by
  simp [emb₂, emb₁, fun₂]

theorem emb₂_of_ne {x : V₂} (h : x ≠ r₂) : emb₂ r₁ r₂ x = Sum.inr ⟨x, h⟩ := by
  simp [emb₂, fun₂, h]

theorem side_emb₁ (x : V₁) : side r₂ (emb₁ r₂ x) = true := rfl

theorem side_emb₂ {x : V₂} (h : x ≠ r₂) : side r₂ (emb₂ r₁ r₂ x) = false := by
  rw [emb₂_of_ne h]
  rfl

theorem emb₂_ne_root {x : V₂} (h : x ≠ r₂) : emb₂ r₁ r₂ x ≠ emb₁ r₂ r₁ := by
  rw [emb₂_of_ne h]
  simp [emb₁]

theorem emb₁_ne_root {x : V₁} (h : x ≠ r₁) : emb₁ r₂ x ≠ emb₁ r₂ r₁ :=
  fun h' => h ((emb₁ r₂).injective h')

theorem mem_glue {H₁ : Finset (Finset V₁)} {H₂ : Finset (Finset V₂)}
    {e : Finset (GVtx (V₁ := V₁) r₂)} :
    e ∈ glue r₁ r₂ H₁ H₂ ↔ e ∈ mapHyp (emb₁ r₂) H₁ ∨ e ∈ mapHyp (emb₂ r₁ r₂) H₂ := by
  simp [glue]

theorem sub₁ (H₁ : Finset (Finset V₁)) (H₂ : Finset (Finset V₂)) :
    mapHyp (emb₁ r₂) H₁ ⊆ glue r₁ r₂ H₁ H₂ :=
  Finset.subset_union_left

theorem sub₂ (H₁ : Finset (Finset V₁)) (H₂ : Finset (Finset V₂)) :
    mapHyp (emb₂ r₁ r₂) H₂ ⊆ glue r₁ r₂ H₁ H₂ :=
  Finset.subset_union_right

theorem side_of_mem₁ {H₁ : Finset (Finset V₁)} {e : Finset (GVtx (V₁ := V₁) r₂)}
    (he : e ∈ mapHyp (emb₁ r₂) H₁) : ∀ x ∈ e, side r₂ x = true := by
  intro x hx
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 he
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  rfl

theorem side_of_mem₂ {H₂ : Finset (Finset V₂)} {e : Finset (GVtx (V₁ := V₁) r₂)}
    (he : e ∈ mapHyp (emb₂ r₁ r₂) H₂) :
    ∀ x ∈ e, x ≠ emb₁ r₂ r₁ → side r₂ x = false := by
  intro x hx hxr
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 he
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  by_cases hy : y = r₂
  · subst hy
    exact absurd emb₂_root hxr
  · exact side_emb₂ hy

theorem localPieces_glue (H₁ : Finset (Finset V₁)) (H₂ : Finset (Finset V₂)) :
    LocalPieces (glue r₁ r₂ H₁ H₂) (emb₁ r₂ r₁) (side r₂) := by
  intro e he x hx y hy hxr hyr
  rcases mem_glue.1 he with he | he
  · rw [side_of_mem₁ he x hx, side_of_mem₁ he y hy]
  · rw [side_of_mem₂ he x hx hxr, side_of_mem₂ he y hy hyr]

theorem exists_emb₁ {x : GVtx (V₁ := V₁) r₂} (h : side r₂ x = true) : ∃ a, emb₁ r₂ a = x := by
  rcases x with a | b
  · exact ⟨a, rfl⟩
  · simp [side] at h

theorem exists_emb₂ {x : GVtx (V₁ := V₁) r₂} (h : side r₂ x = false) :
    ∃ b, b ≠ r₂ ∧ emb₂ r₁ r₂ b = x := by
  rcases x with a | ⟨b, hb⟩
  · simp [side] at h
  · exact ⟨b, hb, emb₂_of_ne hb⟩

theorem isThreeUniform_glue {H₁ : Finset (Finset V₁)} {H₂ : Finset (Finset V₂)}
    (h₁ : IsThreeUniform H₁) (h₂ : IsThreeUniform H₂) : IsThreeUniform (glue r₁ r₂ H₁ H₂) := by
  intro e he
  rcases mem_glue.1 he with he | he
  · exact isThreeUniform_mapHyp h₁ e he
  · exact isThreeUniform_mapHyp h₂ e he

theorem not_containsBergeC5_glue {H₁ : Finset (Finset V₁)} {H₂ : Finset (Finset V₂)}
    (h₁ : IsThreeUniform H₁) (h₂ : IsThreeUniform H₂) (f₁ : ¬ ContainsBergeC5 H₁)
    (f₂ : ¬ ContainsBergeC5 H₂) : ¬ ContainsBergeC5 (glue r₁ r₂ H₁ H₂) := by
  have hu := isThreeUniform_glue (r₁ := r₁) (r₂ := r₂) h₁ h₂
  rintro ⟨v, e, hc⟩
  obtain ⟨p, hp⟩ := cycle_in_piece hu (localPieces_glue H₁ H₂) hc
  have hx : ∀ i, ∃ x ∈ e i, x ≠ emb₁ r₂ r₁ := fun i =>
    exists_ne_of_card_eq_three (hu _ (hc.edges_mem i)) _
  choose x hxe hxr using hx
  cases p with
  | true =>
    have hmem : ∀ i, e i ∈ mapHyp (emb₁ r₂) H₁ := by
      intro i
      rcases mem_glue.1 (hc.edges_mem i) with h | h
      · exact h
      · have h1 := side_of_mem₂ h (x i) (hxe i) (hxr i)
        rw [hp i (x i) (hxe i) (hxr i)] at h1
        exact absurd h1 (by simp)
    exact f₁ (ContainsBergeC5.of_mapHyp ⟨v, e, ⟨hc.vertices_injective, hc.edges_injective,
      hmem, hc.left_mem, hc.right_mem⟩⟩)
  | false =>
    have hmem : ∀ i, e i ∈ mapHyp (emb₂ r₁ r₂) H₂ := by
      intro i
      rcases mem_glue.1 (hc.edges_mem i) with h | h
      · have h1 := side_of_mem₁ h (x i) (hxe i)
        rw [hp i (x i) (hxe i) (hxr i)] at h1
        exact absurd h1 (by simp)
      · exact h
    exact f₂ (ContainsBergeC5.of_mapHyp ⟨v, e, ⟨hc.vertices_injective, hc.edges_injective,
      hmem, hc.left_mem, hc.right_mem⟩⟩)

theorem reach2_glue [Fintype V₁] [Fintype V₂] {H₁ : Finset (Finset V₁)}
    {H₂ : Finset (Finset V₂)} (hr₁ : ∀ u, u ≠ r₁ → Reach2 H₁ r₁ u)
    (hr₂ : ∀ u, u ≠ r₂ → Reach2 H₂ r₂ u) :
    ∀ u, u ≠ emb₁ r₂ r₁ → Reach2 (glue r₁ r₂ H₁ H₂) (emb₁ r₂ r₁) u := by
  intro u hu
  rcases hs : side r₂ u with _ | _
  · obtain ⟨b, hb, rfl⟩ := exists_emb₂ (r₁ := r₁) hs
    have := (hr₂ b hb).map (sub₂ (r₁ := r₁) (r₂ := r₂) H₁ H₂)
    rwa [emb₂_root] at this
  · obtain ⟨a, rfl⟩ := exists_emb₁ hs
    exact (hr₁ a fun h => hu (h ▸ rfl)).map (sub₁ (r₁ := r₁) (r₂ := r₂) H₁ H₂)

theorem pathSaturated_glue [Fintype V₁] [Fintype V₂]
    {H₁ : Finset (Finset V₁)} {H₂ : Finset (Finset V₂)}
    (s₁ : PathSaturated H₁) (s₂ : PathSaturated H₂)
    (hr₁ : ∀ u, u ≠ r₁ → Reach2 H₁ r₁ u) (hr₂ : ∀ u, u ≠ r₂ → Reach2 H₂ r₂ u) :
    PathSaturated (glue r₁ r₂ H₁ H₂) := by
  classical
  have hloc := localPieces_glue (r₁ := r₁) (r₂ := r₂) H₁ H₂
  have hreach := reach2_glue (H₁ := H₁) (H₂ := H₂) hr₁ hr₂
  intro f hf hfH
  by_cases h : ∀ x ∈ f, ∀ y ∈ f, x ≠ emb₁ r₂ r₁ → y ≠ emb₁ r₂ r₁ → side r₂ x = side r₂ y
  · obtain ⟨x₀, hx₀, hx₀r⟩ := exists_ne_of_card_eq_three hf (emb₁ r₂ r₁)
    rcases hp : side r₂ x₀ with _ | _
    · refine path_of_sub (sub₂ (r₁ := r₁) (r₂ := r₂) H₁ H₂) s₂ hf hfH fun y hy => ?_
      by_cases hyr : y = emb₁ r₂ r₁
      · exact ⟨r₂, hyr ▸ emb₂_root⟩
      · obtain ⟨b, -, hb⟩ := exists_emb₂ (r₁ := r₁) ((h y hy x₀ hx₀ hyr hx₀r).trans hp)
        exact ⟨b, hb⟩
    · refine path_of_sub (sub₁ (r₁ := r₁) (r₂ := r₂) H₁ H₂) s₁ hf hfH fun y hy => ?_
      by_cases hyr : y = emb₁ r₂ r₁
      · exact ⟨r₁, hyr.symm⟩
      · exact exists_emb₁ ((h y hy x₀ hx₀ hyr hx₀r).trans hp)
  · simp only [not_forall] at h
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := h
    exact ⟨x, hx, y, hy, path4_of_reach2 hloc hxr hyr hxy (hreach x hxr) (hreach y hyr)⟩

theorem card_glue {H₁ : Finset (Finset V₁)} {H₂ : Finset (Finset V₂)}
    (h₂ : IsThreeUniform H₂) : (glue r₁ r₂ H₁ H₂).card = H₁.card + H₂.card := by
  have hdisj : Disjoint (mapHyp (emb₁ r₂) H₁) (mapHyp (emb₂ r₁ r₂) H₂) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨x, hx, hxr⟩ :=
      exists_ne_of_card_eq_three (isThreeUniform_mapHyp h₂ e he') (emb₁ r₂ r₁)
    have h1 := side_of_mem₁ he x hx
    rw [side_of_mem₂ he' x hx hxr] at h1
    exact absurd h1 (by simp)
  rw [glue, Finset.card_union_of_disjoint hdisj, card_mapHyp, card_mapHyp]

end Glue

/-- **Rooted gluing.** Realizable pairs are closed under addition. -/
theorem Realizable.add {N₁ k₁ N₂ k₂ : ℕ} (h₁ : Realizable N₁ k₁) (h₂ : Realizable N₂ k₂) :
    Realizable (N₁ + N₂) (k₁ + k₂) := by
  obtain ⟨V₁, _, _, r₁, H₁, hc₁, ⟨u₁, f₁, s₁, R₁⟩, hk₁⟩ := h₁
  obtain ⟨V₂, _, _, r₂, H₂, hc₂, ⟨u₂, f₂, s₂, R₂⟩, hk₂⟩ := h₂
  refine ⟨GVtx (V₁ := V₁) r₂, inferInstance, inferInstance, emb₁ r₂ r₁, glue r₁ r₂ H₁ H₂, ?_,
    ⟨isThreeUniform_glue u₁ u₂, not_containsBergeC5_glue u₁ u₂ f₁ f₂,
      pathSaturated_glue s₁ s₂ R₁ R₂, reach2_glue R₁ R₂⟩, ?_⟩
  · have h : Fintype.card {x : V₂ // x ≠ r₂} = N₂ := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hc₂]
      omega
    rw [Fintype.card_sum, hc₁, h]
    omega
  · rw [card_glue u₂, hk₁, hk₂]

end BergeC5
