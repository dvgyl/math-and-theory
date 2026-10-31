import BergeC4.Glue

/-!
# Kernel-checkable certificates for explicit hypergraphs

An explicit hypergraph on `Fin n` is given by a list of triples.  The Boolean functions below
search for the paths and incidences required by the gluing theorem; each comes with a soundness
result: a `true` answer yields the corresponding proposition about the actual hypergraph.  The searches are evaluated by the Lean kernel through `decide +kernel`; no
`native_decide` and no additional axiom is used.
-/

namespace BergeC4

variable {n : ℕ}

/-- A triple of vertices. -/
abbrev Triple (n : ℕ) := Fin n × Fin n × Fin n

/-- The vertex set of a triple. -/
def Triple.toFinset (t : Triple n) : Finset (Fin n) := {t.1, t.2.1, t.2.2}

/-- The hypergraph whose hyperedges are the vertex sets of the listed triples. -/
def ofTriples (L : List (Triple n)) : Finset (Finset (Fin n)) :=
  (L.map Triple.toFinset).toFinset

/-- Membership of a vertex in a triple. -/
def memT (v : Fin n) (t : Triple n) : Bool := v == t.1 || (v == t.2.1 || v == t.2.2)

/-- The three entries of a triple. -/
def verts (t : Triple n) : List (Fin n) := [t.1, t.2.1, t.2.2]

/-- `t` is not contained in `s`, so their vertex sets differ. -/
def neqT (t s : Triple n) : Bool := !(memT t.1 s && (memT t.2.1 s && memT t.2.2 s))

theorem memT_iff {v : Fin n} {t : Triple n} : memT v t = true ↔ v ∈ t.toFinset := by
  simp [memT, Triple.toFinset]

theorem mem_verts {v : Fin n} {t : Triple n} : v ∈ verts t ↔ v ∈ t.toFinset := by
  simp [verts, Triple.toFinset]

theorem mem_ofTriples {L : List (Triple n)} {e : Finset (Fin n)} :
    e ∈ ofTriples L ↔ ∃ t ∈ L, t.toFinset = e := by
  simp [ofTriples]

theorem toFinset_mem_ofTriples {L : List (Triple n)} {t : Triple n} (h : t ∈ L) :
    t.toFinset ∈ ofTriples L :=
  mem_ofTriples.2 ⟨t, h, rfl⟩

theorem ne_of_neqT {t s : Triple n} (h : neqT t s = true) : t.toFinset ≠ s.toFinset := by
  intro heq
  have h1 : memT t.1 s = true := memT_iff.2 (by rw [← heq]; simp [Triple.toFinset])
  have h2 : memT t.2.1 s = true := memT_iff.2 (by rw [← heq]; simp [Triple.toFinset])
  have h3 : memT t.2.2 s = true := memT_iff.2 (by rw [← heq]; simp [Triple.toFinset])
  simp [neqT, h1, h2, h3] at h

/-! ## Uniformity, hubs and edge membership -/

/-- Every listed triple has three distinct entries. -/
def uniformB (L : List (Triple n)) : Bool :=
  L.all fun t => t.1 != t.2.1 && (t.1 != t.2.2 && t.2.1 != t.2.2)

theorem isThreeUniform_of_uniformB {L : List (Triple n)} (h : uniformB L = true) :
    IsThreeUniform (ofTriples L) := by
  intro e he
  obtain ⟨t, ht, rfl⟩ := mem_ofTriples.1 he
  simp only [uniformB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h12, h13, h23⟩ := h t ht
  exact Finset.card_eq_three.2 ⟨_, _, _, h12, h13, h23, rfl⟩

theorem subset_of_neqT_eq_false {t s : Triple n} (h : neqT t s = false) :
    t.toFinset ⊆ s.toFinset := by
  simp only [neqT, Bool.not_eq_false', Bool.and_eq_true] at h
  obtain ⟨a, b, c⟩ := h
  intro y hy
  simp only [Triple.toFinset, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · exact memT_iff.1 a
  · exact memT_iff.1 b
  · exact memT_iff.1 c

theorem neqT_or_neqT {t s : Triple n} (h : t.toFinset ≠ s.toFinset) :
    neqT t s = true ∨ neqT s t = true := by
  by_contra hc
  simp only [not_or, Bool.not_eq_true] at hc
  exact h (Finset.Subset.antisymm (subset_of_neqT_eq_false hc.1) (subset_of_neqT_eq_false hc.2))

/-- The vertex `v` is below `k`, or lies in no two triples with different vertex sets. -/
def hubB (L : List (Triple n)) (k : ℕ) (v : Fin n) : Bool :=
  decide (v.val < k) || L.all fun t₁ => L.all fun t₂ => !(neqT t₁ t₂ && (memT v t₁ && memT v t₂))

/-- If only the vertices `0, 1, 2` lie in two distinct hyperedges, there is no Berge-`C₄`. -/
theorem not_containsBergeC4_of_hubB {L : List (Triple n)} (h : ∀ v : Fin n, hubB L 3 v = true) :
    ¬ ContainsBergeC4 (ofTriples L) := by
  classical
  refine not_containsBergeC4_of_hubs ((Finset.univ : Finset (Fin n)).filter fun v => v.val < 3)
    ?_ ?_
  · have hsub : ((Finset.univ : Finset (Fin n)).filter fun v => v.val < 3).map Fin.valEmbedding
        ⊆ Finset.range 3 := by
      intro x hx
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      simpa using hv
    simpa using Finset.card_le_card hsub
  · intro x e₁ he₁ e₂ he₂ hne hx₁ hx₂
    obtain ⟨t₁, ht₁, rfl⟩ := mem_ofTriples.1 he₁
    obtain ⟨t₂, ht₂, rfl⟩ := mem_ofTriples.1 he₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := h x
    simp only [hubB, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hx
    rcases hx with hx | hx
    · exact hx
    · exfalso
      have m1 := memT_iff.2 hx₁
      have m2 := memT_iff.2 hx₂
      rcases neqT_or_neqT hne with hn | hn
      · have key := hx t₁ ht₁ t₂ ht₂
        simp [hn, m1, m2] at key
      · have key := hx t₂ ht₂ t₁ ht₁
        simp [hn, m1, m2] at key

/-- All three vertices lie in one listed triple. -/
def isEdgeB (L : List (Triple n)) (a b c : Fin n) : Bool :=
  L.any fun t => memT a t && (memT b t && memT c t)

theorem mem_of_isEdgeB {L : List (Triple n)} {a b c : Fin n} (h : isEdgeB L a b c = true)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ({a, b, c} : Finset (Fin n)) ∈ ofTriples L := by
  simp only [isEdgeB, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨t, ht, ha, hb, hc⟩ := h
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ t.toFinset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact memT_iff.1 ha
    · exact memT_iff.1 hb
    · exact memT_iff.1 hc
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩]
    exact Finset.card_le_three)
  rw [heq]
  exact toFinset_mem_ofTriples ht

/-! ## Paths -/

/-- Search for a three-edge Berge path from `a` to `b` through listed triples. -/
def pathB (L : List (Triple n)) (a b : Fin n) : Bool :=
  a != b && L.any fun t₁ => memT a t₁ && L.any fun t₂ => neqT t₁ t₂ && L.any fun t₃ =>
    neqT t₁ t₃ && (neqT t₂ t₃ && (memT b t₃ && (verts t₁).any fun p =>
      p != a && (p != b && (memT p t₂ && (verts t₂).any fun q =>
        q != a && (q != b && (q != p && memT q t₃))))))

theorem path3_of_pathB {L : List (Triple n)} {a b : Fin n} (h : pathB L a b = true) :
    Path3 (ofTriples L) a b := by
  simp only [pathB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq, memT_iff,
    mem_verts] at h
  obtain ⟨hab, t₁, ht₁, ha1, t₂, ht₂, n12, t₃, ht₃, n13, n23, hb3, p, hp1, hpa, hpb, hp2, q,
    hq2, hqa, hqb, hqp, hq3⟩ := h
  exact ⟨p, q, t₁.toFinset, t₂.toFinset, t₃.toFinset, toFinset_mem_ofTriples ht₁,
    toFinset_mem_ofTriples ht₂, toFinset_mem_ofTriples ht₃, ne_of_neqT n12, ne_of_neqT n13,
    ne_of_neqT n23, Ne.symm hpa, Ne.symm hqa, hab, Ne.symm hqp, hpb, hqb, ha1, hp1, hp2, hq2,
    hq3, hb3⟩

/-- Search for a one-edge path from `a` to the root `r`. -/
def reach1B (L : List (Triple n)) (r a : Fin n) : Bool :=
  L.any fun t => memT r t && memT a t

/-- Search for a two-edge path from `a` to the root `r`. -/
def reach2B (L : List (Triple n)) (r a : Fin n) : Bool :=
  L.any fun t₁ => memT a t₁ && L.any fun t₂ => neqT t₁ t₂ && (memT r t₂ &&
    (verts t₁).any fun w => w != a && (w != r && memT w t₂))

theorem reach1_of_reach1B {L : List (Triple n)} {r a : Fin n} (h : reach1B L r a = true) :
    Reach1 (ofTriples L) r a := by
  simp only [reach1B, List.any_eq_true, Bool.and_eq_true, memT_iff] at h
  obtain ⟨t, ht, hr, ha⟩ := h
  exact ⟨t.toFinset, toFinset_mem_ofTriples ht, ha, hr⟩

theorem reach2_of_reach2B {L : List (Triple n)} {r a : Fin n} (h : reach2B L r a = true) :
    Reach2 (ofTriples L) r a := by
  simp only [reach2B, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq, memT_iff,
    mem_verts] at h
  obtain ⟨t₁, ht₁, ha1, t₂, ht₂, n12, hr2, w, hw1, hwa, hwr, hw2⟩ := h
  exact ⟨w, t₁.toFinset, toFinset_mem_ofTriples ht₁, t₂.toFinset, toFinset_mem_ofTriples ht₂,
    ne_of_neqT n12, Ne.symm hwa, hwr, ha1, hw1, hw2, hr2⟩

/-! ## Saturation -/

theorem exists_sorted {x y z : Fin n} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b c : Fin n, a < b ∧ b < c ∧ ({x, y, z} : Finset (Fin n)) = {a, b, c} := by
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  all_goals first
    | exact ⟨x, y, z, ‹_›, ‹_›, rfl⟩
    | exact ⟨x, z, y, ‹_›, ‹_›, by ext; simp; tauto⟩
    | exact ⟨y, x, z, ‹_›, ‹_›, by ext; simp; tauto⟩
    | exact ⟨y, z, x, ‹_›, ‹_›, by ext; simp; tauto⟩
    | exact ⟨z, x, y, ‹_›, ‹_›, by ext; simp; tauto⟩
    | exact ⟨z, y, x, ‹_›, ‹_›, by ext; simp; tauto⟩

/-- Every increasing triple of vertices is a listed hyperedge or contains the ends of a
three-edge path. -/
def SatCheck (L : List (Triple n)) : Prop :=
  ∀ a b c : Fin n, a < b → b < c →
    (isEdgeB L a b c || (pathB L a b || (pathB L a c || pathB L b c))) = true

instance (L : List (Triple n)) : Decidable (SatCheck L) := by
  unfold SatCheck
  infer_instance

theorem pathSaturated_of_satCheck {L : List (Triple n)} (h : SatCheck L) :
    PathSaturated (ofTriples L) := by
  intro f hf hfH
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hf
  obtain ⟨a, b, c, hab, hbc, habc⟩ := exists_sorted hxy hxz hyz
  rw [habc] at hfH ⊢
  have hac : a < c := hab.trans hbc
  have key := h a b c hab hbc
  simp only [Bool.or_eq_true] at key
  rcases key with h1 | h1 | h1 | h1
  · exact absurd (mem_of_isEdgeB h1 hab.ne hac.ne hbc.ne) hfH
  · exact ⟨a, by simp, b, by simp, path3_of_pathB h1⟩
  · exact ⟨a, by simp, c, by simp, path3_of_pathB h1⟩
  · exact ⟨b, by simp, c, by simp, path3_of_pathB h1⟩

/-- An explicit hypergraph passing the uniformity, hub and saturation checks is
Berge-`C₄`-saturated. -/
theorem isBergeC4Saturated_ofTriples {L : List (Triple n)} (hu : uniformB L = true)
    (hfree : ¬ ContainsBergeC4 (ofTriples L)) (hs : SatCheck L) :
    IsBergeC4Saturated (ofTriples L) :=
  isBergeC4Saturated_of_pathSaturated (isThreeUniform_of_uniformB hu) hfree
    (pathSaturated_of_satCheck hs)

end BergeC4
