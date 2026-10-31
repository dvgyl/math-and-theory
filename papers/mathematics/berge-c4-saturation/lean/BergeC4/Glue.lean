import BergeC4.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin

/-!
# Gluing saturated pieces at a common root

A hypergraph whose vertex set is split into *pieces* that meet only in a root vertex `r`
(every hyperedge has all its non-root vertices in one piece) contains a Berge-`C₄` only inside a
single piece: around a Berge-`C₄` at most one cycle vertex is the root, and every other cycle
vertex forces its two cycle hyperedges into the same piece.  An absent triple that meets two
pieces outside the root is closed by a path through the root of lengths one and two on the two
sides.

We apply this to one base hypergraph on `Fin n₀`, whose root is `0`, glued at the root to `t`
copies of a five-vertex block on `Fin 5`, whose root is also `0`.
-/

namespace BergeC4

section Generic

variable {V W P : Type*}

/-- A one-edge Berge path from `u` to the root `r`. -/
def Reach1 (H : Finset (Finset V)) (r u : V) : Prop :=
  ∃ e ∈ H, u ∈ e ∧ r ∈ e

/-- A two-edge Berge path `u, w, r` through distinct hyperedges. -/
def Reach2 (H : Finset (Finset V)) (r u : V) : Prop :=
  ∃ w, ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ u ≠ w ∧ w ≠ r ∧ u ∈ e₁ ∧ w ∈ e₁ ∧ w ∈ e₂ ∧ r ∈ e₂

theorem Reach1.map {g : W ↪ V} {B : Finset (Finset W)} {H : Finset (Finset V)}
    (hBH : mapHyp g B ⊆ H) {r u : W} (h : Reach1 B r u) : Reach1 H (g r) (g u) := by
  obtain ⟨e, he, hu, hr⟩ := h
  exact ⟨e.map g, hBH (mem_mapHyp.2 he), Finset.mem_map_of_mem g hu, Finset.mem_map_of_mem g hr⟩

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

/-- A Berge-`C₄` of a hypergraph with local pieces has all its hyperedges in one piece. -/
theorem not_containsBergeC4_of_pieces {H : Finset (Finset V)} {r : V} {π : V → P}
    (hu : IsThreeUniform H) (hloc : LocalPieces H r π)
    (hpiece : ∀ (p : P) v e, IsBergeC4 H v e → (∀ i, ∀ x ∈ e i, x ≠ r → π x = p) → False) :
    ¬ ContainsBergeC4 H := by
  rintro ⟨v, e, hc⟩
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
  have l3 : v 0 ≠ r → π (w 3) = π (w 0) := hlink 3
  have hall : π (w 1) = π (w 0) ∧ π (w 2) = π (w 0) ∧ π (w 3) = π (w 0) := by
    by_cases h0 : v 0 = r
    · have a := l0 (hne 0 1 (by decide) h0)
      have b := l1 (hne 0 2 (by decide) h0)
      have d := l2 (hne 0 3 (by decide) h0)
      exact ⟨a.symm, (a.trans b).symm, (a.trans (b.trans d)).symm⟩
    · have d3 := l3 h0
      by_cases h1 : v 1 = r
      · have b := l1 (hne 1 2 (by decide) h1)
        have d := l2 (hne 1 3 (by decide) h1)
        exact ⟨b.trans (d.trans d3), d.trans d3, d3⟩
      · have a := l0 h1
        by_cases h2 : v 2 = r
        · have d := l2 (hne 2 3 (by decide) h2)
          exact ⟨a.symm, d.trans d3, d3⟩
        · have b := l1 h2
          exact ⟨a.symm, (a.trans b).symm, d3⟩
  refine hpiece (π (w 0)) v e hc fun i x hx hxr => (hcx i x hx hxr).trans ?_
  fin_cases i
  · rfl
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2

/-- A one-edge path to the root on one side and a two-edge path on the other give a
three-edge path between vertices of different pieces. -/
theorem path3_of_reach {H : Finset (Finset V)} {r : V} {π : V → P} (hloc : LocalPieces H r π)
    {u w : V} (hu : u ≠ r) (hw : w ≠ r) (hπ : π u ≠ π w) (h1 : Reach1 H r u)
    (h2 : Reach2 H r w) : Path3 H u w := by
  obtain ⟨e, he, hue, hre⟩ := h1
  obtain ⟨x, e₁, he₁, e₂, he₂, h12, hwx, hxr, hw1, hx1, hx2, hr2⟩ := h2
  have hπx : π x = π w := hloc e₁ he₁ x hx1 w hw1 hxr hw
  have hux : u ≠ x := fun h => hπ (by rw [h, hπx])
  have hee₂ : e ≠ e₂ := fun h => hπ (by rw [hloc e he u hue x (h ▸ hx2) hu hxr, hπx])
  have hee₁ : e ≠ e₁ := fun h => hπ (hloc e he u hue w (h ▸ hw1) hu hw)
  exact ⟨r, x, e, e₂, e₁, he, he₂, he₁, hee₂, hee₁, h12.symm, hu, hux,
    fun h => hπ (congrArg π h), hxr.symm, hw.symm, hwx.symm, hue, hre, hr2, hx2, hx1, hw1⟩

/-- Saturation of a hypergraph with local pieces, from cross-piece paths and saturation inside
each piece. -/
theorem pathSaturated_of_pieces {H : Finset (Finset V)} {r : V} {π : V → P}
    (hcross : ∀ u w, u ≠ r → w ≠ r → π u ≠ π w → Path3 H u w)
    (hlocal : ∀ f : Finset V, f.card = 3 → f ∉ H →
      (∀ x ∈ f, ∀ y ∈ f, x ≠ r → y ≠ r → π x = π y) → ∃ a ∈ f, ∃ b ∈ f, Path3 H a b) :
    PathSaturated H := by
  intro f hf hfH
  by_cases h : ∀ x ∈ f, ∀ y ∈ f, x ≠ r → y ≠ r → π x = π y
  · exact hlocal f hf hfH h
  · simp only [not_forall] at h
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := h
    exact ⟨x, hx, y, hy, hcross x y hxr hyr hxy⟩

/-- An absent triple inside the image of a path-saturated hypergraph contains the ends of a
three-edge path. -/
theorem path_of_sub [Fintype W] [DecidableEq W] [DecidableEq V] {g : W ↪ V}
    {B : Finset (Finset W)} {H : Finset (Finset V)} (hBH : mapHyp g B ⊆ H) (hB : PathSaturated B)
    {f : Finset V} (hf : f.card = 3) (hfH : f ∉ H) (hrange : ∀ x ∈ f, ∃ y, g y = x) :
    ∃ a ∈ f, ∃ b ∈ f, Path3 H a b := by
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

end Generic

section Construction

variable (n₀ t : ℕ) [NeZero n₀]

/-- Vertices: a base copy of `Fin n₀` and `t` blocks of four further vertices. -/
abbrev Vtx := Fin n₀ ⊕ (Fin t × Fin 4)

/-- The common root, vertex `0` of the base. -/
def root : Vtx n₀ t := Sum.inl 0

/-- The piece of a vertex: `none` for the base, `some j` for block `j`. -/
def piece : Vtx n₀ t → Option (Fin t)
  | Sum.inl _ => none
  | Sum.inr (j, _) => some j

/-- The base embedding. -/
def baseEmb : Fin n₀ ↪ Vtx n₀ t := ⟨Sum.inl, Sum.inl_injective⟩

/-- Block `j` as an image of `Fin 5`: vertex `0` goes to the root and `k + 1` to `(j, k)`. -/
def blockFun (j : Fin t) : Fin 5 → Vtx n₀ t :=
  Fin.cases (root n₀ t) fun k => Sum.inr (j, k)

theorem blockFun_injective (j : Fin t) : Function.Injective (blockFun n₀ t j) := by
  intro a b h
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp_all [blockFun, root]

/-- The block embedding. -/
def blockEmb (j : Fin t) : Fin 5 ↪ Vtx n₀ t := ⟨blockFun n₀ t j, blockFun_injective n₀ t j⟩

/-- The base hypergraph `B` glued at the root to `t` copies of the block hypergraph `K`. -/
def glued (B : Finset (Finset (Fin n₀))) (K : Finset (Finset (Fin 5))) :
    Finset (Finset (Vtx n₀ t)) :=
  mapHyp (baseEmb n₀ t) B ∪ Finset.univ.biUnion fun j => mapHyp (blockEmb n₀ t j) K

variable {n₀ t}

theorem baseEmb_zero : baseEmb n₀ t 0 = root n₀ t := rfl

theorem blockEmb_zero (j : Fin t) : blockEmb n₀ t j 0 = root n₀ t := rfl

theorem blockEmb_succ (j : Fin t) (k : Fin 4) : blockEmb n₀ t j k.succ = Sum.inr (j, k) := rfl

omit [NeZero n₀] in
theorem piece_of_mem_base {B : Finset (Finset (Fin n₀))} {e : Finset (Vtx n₀ t)}
    (he : e ∈ mapHyp (baseEmb n₀ t) B) : ∀ x ∈ e, piece n₀ t x = none := by
  intro x hx
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 he
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  rfl

theorem piece_blockEmb {j : Fin t} {k : Fin 5} (h : blockEmb n₀ t j k ≠ root n₀ t) :
    piece n₀ t (blockEmb n₀ t j k) = some j := by
  cases k using Fin.cases with
  | zero => exact absurd rfl h
  | succ k => rfl

theorem piece_of_mem_block {K : Finset (Finset (Fin 5))} {j : Fin t} {e : Finset (Vtx n₀ t)}
    (he : e ∈ mapHyp (blockEmb n₀ t j) K) : ∀ x ∈ e, x ≠ root n₀ t → piece n₀ t x = some j := by
  intro x hx hxr
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 he
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  exact piece_blockEmb hxr

theorem mem_glued {B : Finset (Finset (Fin n₀))} {K : Finset (Finset (Fin 5))}
    {e : Finset (Vtx n₀ t)} :
    e ∈ glued n₀ t B K ↔ e ∈ mapHyp (baseEmb n₀ t) B ∨ ∃ j, e ∈ mapHyp (blockEmb n₀ t j) K := by
  simp [glued]

theorem base_sub_glued (B : Finset (Finset (Fin n₀))) (K : Finset (Finset (Fin 5))) :
    mapHyp (baseEmb n₀ t) B ⊆ glued n₀ t B K :=
  Finset.subset_union_left

theorem block_sub_glued (B : Finset (Finset (Fin n₀))) (K : Finset (Finset (Fin 5)))
    (j : Fin t) : mapHyp (blockEmb n₀ t j) K ⊆ glued n₀ t B K := fun _ he =>
  mem_glued.2 (Or.inr ⟨j, he⟩)

theorem isThreeUniform_mapHyp {g : W ↪ V} {B : Finset (Finset W)} (hB : IsThreeUniform B) :
    IsThreeUniform (mapHyp g B) := by
  intro e he
  obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 he
  simpa using hB s hs

theorem isThreeUniform_glued {B : Finset (Finset (Fin n₀))} {K : Finset (Finset (Fin 5))}
    (hB : IsThreeUniform B) (hK : IsThreeUniform K) : IsThreeUniform (glued n₀ t B K) := by
  intro e he
  rcases mem_glued.1 he with he | ⟨j, he⟩
  · exact isThreeUniform_mapHyp hB e he
  · exact isThreeUniform_mapHyp hK e he

theorem localPieces_glued (B : Finset (Finset (Fin n₀))) (K : Finset (Finset (Fin 5))) :
    LocalPieces (glued n₀ t B K) (root n₀ t) (piece n₀ t) := by
  intro e he x hx y hy hxr hyr
  rcases mem_glued.1 he with he | ⟨j, he⟩
  · rw [piece_of_mem_base he x hx, piece_of_mem_base he y hy]
  · rw [piece_of_mem_block he x hx hxr, piece_of_mem_block he y hy hyr]

omit [NeZero n₀] in
/-- A non-root vertex of piece `none` is a base vertex. -/
theorem exists_base_of_piece {x : Vtx n₀ t} (h : piece n₀ t x = none) :
    ∃ a, baseEmb n₀ t a = x := by
  rcases x with a | ⟨j, k⟩
  · exact ⟨a, rfl⟩
  · simp [piece] at h

/-- A vertex of piece `some j` is a non-root vertex of block `j`. -/
theorem exists_block_of_piece {x : Vtx n₀ t} {j : Fin t} (h : piece n₀ t x = some j) :
    ∃ k : Fin 4, blockEmb n₀ t j k.succ = x := by
  rcases x with a | ⟨j', k⟩
  · simp [piece] at h
  · simp only [piece, Option.some.injEq] at h
    subst h
    exact ⟨k, rfl⟩

theorem not_containsBergeC4_glued {B : Finset (Finset (Fin n₀))} {K : Finset (Finset (Fin 5))}
    (hB : IsThreeUniform B) (hK : IsThreeUniform K) (hBfree : ¬ ContainsBergeC4 B)
    (hKcard : K.card < 4) : ¬ ContainsBergeC4 (glued n₀ t B K) := by
  have hu := isThreeUniform_glued (t := t) hB hK
  refine not_containsBergeC4_of_pieces hu (localPieces_glued B K) ?_
  intro p v e hc hp
  have hx : ∀ i, ∃ x ∈ e i, x ≠ root n₀ t := fun i =>
    exists_ne_of_card_eq_three (hu _ (hc.edges_mem i)) _
  choose x hxe hxr using hx
  cases p with
  | none =>
    have hmem : ∀ i, e i ∈ mapHyp (baseEmb n₀ t) B := by
      intro i
      rcases mem_glued.1 (hc.edges_mem i) with h | ⟨j, h⟩
      · exact h
      · have h1 := piece_of_mem_block h (x i) (hxe i) (hxr i)
        rw [hp i (x i) (hxe i) (hxr i)] at h1
        exact absurd h1 (by simp)
    exact hBfree (ContainsBergeC4.of_mapHyp ⟨v, e, ⟨hc.vertices_injective, hc.edges_injective,
      hmem, hc.left_mem, hc.right_mem⟩⟩)
  | some j =>
    have hmem : ∀ i, e i ∈ mapHyp (blockEmb n₀ t j) K := by
      intro i
      rcases mem_glued.1 (hc.edges_mem i) with h | ⟨j', h⟩
      · have h1 := piece_of_mem_base h (x i) (hxe i)
        rw [hp i (x i) (hxe i) (hxr i)] at h1
        exact absurd h1 (by simp)
      · have h1 := piece_of_mem_block h (x i) (hxe i) (hxr i)
        rw [hp i (x i) (hxe i) (hxr i), Option.some.injEq] at h1
        exact h1 ▸ h
    have hc' : ContainsBergeC4 (mapHyp (blockEmb n₀ t j) K) :=
      ⟨v, e, ⟨hc.vertices_injective, hc.edges_injective, hmem, hc.left_mem, hc.right_mem⟩⟩
    have := hc'.four_le_card
    rw [card_mapHyp] at this
    omega

theorem pathSaturated_glued {B : Finset (Finset (Fin n₀))} {K : Finset (Finset (Fin 5))}
    (hBsat : PathSaturated B) (hBreach : ∀ a : Fin n₀, a ≠ 0 → Reach1 B 0 a ∨ Reach2 B 0 a)
    (hKsat : PathSaturated K) (hKreach : ∀ a : Fin 5, a ≠ 0 → Reach1 K 0 a ∧ Reach2 K 0 a) :
    PathSaturated (glued n₀ t B K) := by
  classical
  have hloc := localPieces_glued (t := t) B K
  -- a base vertex and a vertex of block `j` are joined by a three-edge path
  have hbb : ∀ (a : Fin n₀) (j : Fin t) (k : Fin 4), a ≠ 0 →
      Path3 (glued n₀ t B K) (baseEmb n₀ t a) (blockEmb n₀ t j k.succ) := by
    intro a j k ha
    have hu : baseEmb n₀ t a ≠ root n₀ t := fun h => ha (Sum.inl_injective h)
    have hw : blockEmb n₀ t j k.succ ≠ root n₀ t := by simp [blockEmb_succ, root]
    have hπ : piece n₀ t (baseEmb n₀ t a) ≠ piece n₀ t (blockEmb n₀ t j k.succ) := by
      simp [baseEmb, blockEmb_succ, piece]
    obtain ⟨hK1, hK2⟩ := hKreach k.succ (Fin.succ_ne_zero k)
    have hK1' := hK1.map (block_sub_glued B K j)
    have hK2' := hK2.map (block_sub_glued B K j)
    rw [blockEmb_zero] at hK1' hK2'
    rcases hBreach a ha with hB1 | hB2
    · have hB1' := hB1.map (base_sub_glued (t := t) B K)
      rw [baseEmb_zero] at hB1'
      exact path3_of_reach hloc hu hw hπ hB1' hK2'
    · have hB2' := hB2.map (base_sub_glued (t := t) B K)
      rw [baseEmb_zero] at hB2'
      exact (path3_of_reach hloc hw hu (Ne.symm hπ) hK1' hB2').symm
  refine pathSaturated_of_pieces (r := root n₀ t) (π := piece n₀ t) ?_ ?_
  · intro u w hu hw hπ
    rcases hpu : piece n₀ t u with _ | j <;> rcases hpw : piece n₀ t w with _ | j'
    · exact absurd (hpu.trans hpw.symm) hπ
    · obtain ⟨a, rfl⟩ := exists_base_of_piece hpu
      obtain ⟨k, rfl⟩ := exists_block_of_piece hpw
      exact hbb a j' k fun h => hu (by rw [h, baseEmb_zero])
    · obtain ⟨a, rfl⟩ := exists_base_of_piece hpw
      obtain ⟨k, rfl⟩ := exists_block_of_piece hpu
      exact (hbb a j k fun h => hw (by rw [h, baseEmb_zero])).symm
    · obtain ⟨k, rfl⟩ := exists_block_of_piece hpu
      obtain ⟨k', rfl⟩ := exists_block_of_piece hpw
      obtain ⟨-, hK2⟩ := hKreach k'.succ (Fin.succ_ne_zero k')
      obtain ⟨hK1, -⟩ := hKreach k.succ (Fin.succ_ne_zero k)
      have hK1' := hK1.map (block_sub_glued B K j)
      have hK2' := hK2.map (block_sub_glued B K j')
      rw [blockEmb_zero] at hK1' hK2'
      exact path3_of_reach hloc hu hw hπ hK1' hK2'
  · intro f hf hfH hsame
    obtain ⟨x₀, hx₀, hx₀r⟩ := exists_ne_of_card_eq_three hf (root n₀ t)
    rcases hp : piece n₀ t x₀ with _ | j
    · refine path_of_sub (base_sub_glued B K) hBsat hf hfH fun y hy => ?_
      by_cases hyr : y = root n₀ t
      · exact ⟨0, hyr.symm⟩
      · exact exists_base_of_piece ((hsame y hy x₀ hx₀ hyr hx₀r).trans hp)
    · refine path_of_sub (block_sub_glued B K j) hKsat hf hfH fun y hy => ?_
      by_cases hyr : y = root n₀ t
      · exact ⟨0, hyr.symm⟩
      · obtain ⟨k, hk⟩ := exists_block_of_piece ((hsame y hy x₀ hx₀ hyr hx₀r).trans hp)
        exact ⟨k.succ, hk⟩

theorem card_glued {B : Finset (Finset (Fin n₀))} {K : Finset (Finset (Fin 5))}
    (hB : IsThreeUniform B) (hK : IsThreeUniform K) :
    (glued n₀ t B K).card = B.card + t * K.card := by
  classical
  have hdisj : Disjoint (mapHyp (baseEmb n₀ t) B)
      (Finset.univ.biUnion fun j => mapHyp (blockEmb n₀ t j) K) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨j, -, he'⟩ := Finset.mem_biUnion.1 he'
    obtain ⟨x, hx, hxr⟩ := exists_ne_of_card_eq_three (isThreeUniform_mapHyp hB e he) (root n₀ t)
    have h1 := piece_of_mem_base he x hx
    rw [piece_of_mem_block he' x hx hxr] at h1
    exact absurd h1 (by simp)
  have hpair : ((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint
      fun j => mapHyp (blockEmb n₀ t j) K := by
    intro j _ j' _ hjj'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨x, hx, hxr⟩ := exists_ne_of_card_eq_three (isThreeUniform_mapHyp hK e he) (root n₀ t)
    have h1 := piece_of_mem_block he x hx hxr
    rw [piece_of_mem_block he' x hx hxr, Option.some.injEq] at h1
    exact hjj' h1.symm
  rw [glued, Finset.card_union_of_disjoint hdisj, Finset.card_biUnion hpair, card_mapHyp]
  simp [card_mapHyp]

omit [NeZero n₀] in
theorem card_vtx : Fintype.card (Vtx n₀ t) = n₀ + 4 * t := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- **Rooted gluing.** A Berge-`C₄`-free, path-saturated base whose non-root vertices all have a
one- or two-edge path to the root `0`, glued at the root to `t` copies of a three-edge
path-saturated block on `Fin 5` whose non-root vertices have both, is Berge-`C₄`-saturated. -/
theorem glued_saturated {B : Finset (Finset (Fin n₀))} {K : Finset (Finset (Fin 5))}
    (hB : IsThreeUniform B) (hBfree : ¬ ContainsBergeC4 B) (hBsat : PathSaturated B)
    (hBreach : ∀ a : Fin n₀, a ≠ 0 → Reach1 B 0 a ∨ Reach2 B 0 a)
    (hK : IsThreeUniform K) (hKcard : K.card = 3) (hKsat : PathSaturated K)
    (hKreach : ∀ a : Fin 5, a ≠ 0 → Reach1 K 0 a ∧ Reach2 K 0 a) :
    IsBergeC4Saturated (glued n₀ t B K) ∧ (glued n₀ t B K).card = B.card + 3 * t := by
  refine ⟨isBergeC4Saturated_of_pathSaturated (isThreeUniform_glued hB hK)
    (not_containsBergeC4_glued hB hK hBfree (by omega))
    (pathSaturated_glued hBsat hBreach hKsat hKreach), ?_⟩
  rw [card_glued hB hK, hKcard, mul_comm]

/-- The glued hypergraph, relabelled to the vertex set `Fin n` with `n = n₀ + 4t`. -/
theorem exists_saturated_of_base {B : Finset (Finset (Fin n₀))} {K : Finset (Finset (Fin 5))}
    (hB : IsThreeUniform B) (hBfree : ¬ ContainsBergeC4 B) (hBsat : PathSaturated B)
    (hBreach : ∀ a : Fin n₀, a ≠ 0 → Reach1 B 0 a ∨ Reach2 B 0 a)
    (hK : IsThreeUniform K) (hKcard : K.card = 3) (hKsat : PathSaturated K)
    (hKreach : ∀ a : Fin 5, a ≠ 0 → Reach1 K 0 a ∧ Reach2 K 0 a) (t n : ℕ)
    (hn : n₀ + 4 * t = n) :
    ∃ H : Finset (Finset (Fin n)), IsBergeC4Saturated H ∧ H.card = B.card + 3 * t := by
  classical
  obtain ⟨hsat, hcard⟩ := glued_saturated (t := t) hB hBfree hBsat hBreach hK hKcard hKsat hKreach
  let e : Vtx n₀ t ≃ Fin n := Fintype.equivFinOfCardEq (card_vtx.trans hn)
  exact ⟨relabel e (glued n₀ t B K), hsat.relabel e, by rw [card_relabel, hcard]⟩

end Construction

end BergeC4
