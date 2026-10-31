import BergeC5.Glue

/-!
# Kernel-checkable certificates for explicit hypergraphs

An explicit hypergraph on `Fin n` is given by a list of triples.  The Boolean functions below
search for the paths, cycles and incidences used by the gluing theorem; each comes with a
soundness result relating a Boolean answer to the corresponding proposition about the actual
hypergraph.  The searches are evaluated by the Lean kernel through `decide +kernel`; no
`native_decide` and no additional axiom is used.
-/

namespace BergeC5

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

/-- The vertex sets of `t` and `s` differ. -/
def diffT (t s : Triple n) : Bool := neqT t s || neqT s t

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

theorem diffT_iff {t s : Triple n} : diffT t s = true ↔ t.toFinset ≠ s.toFinset := by
  constructor
  · intro h
    simp only [diffT, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ne_of_neqT h
    · exact fun e => ne_of_neqT h e.symm
  · intro h
    by_contra hc
    simp only [diffT, Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    exact h (Finset.Subset.antisymm (subset_of_neqT_eq_false hc.1)
      (subset_of_neqT_eq_false hc.2))

/-! ## Uniformity and edge membership -/

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

/-- Search for a four-edge Berge path from `a` to `b` through listed triples. -/
def pathB (L : List (Triple n)) (a b : Fin n) : Bool :=
  a != b && L.any fun t₁ => memT a t₁ && (verts t₁).any fun p =>
    p != a && (p != b && L.any fun t₂ => neqT t₁ t₂ && (memT p t₂ && (verts t₂).any fun q =>
      q != a && (q != b && (q != p && L.any fun t₃ => neqT t₁ t₃ && (neqT t₂ t₃ &&
        (memT q t₃ && (verts t₃).any fun s =>
          s != a && (s != b && (s != p && (s != q && L.any fun t₄ =>
            neqT t₁ t₄ && (neqT t₂ t₄ && (neqT t₃ t₄ && (memT s t₄ && memT b t₄))))))))))))

theorem path4_of_pathB {L : List (Triple n)} {a b : Fin n} (h : pathB L a b = true) :
    Path4 (ofTriples L) a b := by
  simp only [pathB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq, memT_iff,
    mem_verts] at h
  obtain ⟨hab, t₁, ht₁, ha1, p, hp1, hpa, hpb, t₂, ht₂, n12, hp2, q, hq2, hqa, hqb, hqp,
    t₃, ht₃, n13, n23, hq3, s, hs3, hsa, hsb, hsp, hsq, t₄, ht₄, n14, n24, n34, hs4, hb4⟩ := h
  exact ⟨p, q, s, t₁.toFinset, t₂.toFinset, t₃.toFinset, t₄.toFinset,
    toFinset_mem_ofTriples ht₁, toFinset_mem_ofTriples ht₂, toFinset_mem_ofTriples ht₃,
    toFinset_mem_ofTriples ht₄, ne_of_neqT n12, ne_of_neqT n13, ne_of_neqT n14,
    ne_of_neqT n23, ne_of_neqT n24, ne_of_neqT n34, Ne.symm hpa, Ne.symm hqa, Ne.symm hsa, hab,
    Ne.symm hqp, Ne.symm hsp, hpb, Ne.symm hsq, hqb, hsb, ha1, hp1, hp2, hq2, hq3, hs3, hs4,
    hb4⟩

/-- Search for a two-edge path from `a` to the root `r`. -/
def reach2B (L : List (Triple n)) (r a : Fin n) : Bool :=
  L.any fun t₁ => memT a t₁ && L.any fun t₂ => neqT t₁ t₂ && (memT r t₂ &&
    (verts t₁).any fun w => w != a && (w != r && memT w t₂))

theorem reach2_of_reach2B {L : List (Triple n)} {r a : Fin n} (h : reach2B L r a = true) :
    Reach2 (ofTriples L) r a := by
  simp only [reach2B, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq, memT_iff,
    mem_verts] at h
  obtain ⟨t₁, ht₁, ha1, t₂, ht₂, n12, hr2, w, hw1, hwa, hwr, hw2⟩ := h
  exact ⟨w, t₁.toFinset, toFinset_mem_ofTriples ht₁, t₂.toFinset, toFinset_mem_ofTriples ht₂,
    ne_of_neqT n12, Ne.symm hwa, hwr, ha1, hw1, hw2, hr2⟩

/-! ## Cycles -/

/-- Search for a Berge-`C₅` among the listed triples. -/
def cycleB (L : List (Triple n)) : Bool :=
  L.any fun t₀ => (verts t₀).any fun v₀ => (verts t₀).any fun v₁ => v₁ != v₀ &&
    L.any fun t₁ => diffT t₀ t₁ && (memT v₁ t₁ && (verts t₁).any fun v₂ =>
      v₂ != v₀ && (v₂ != v₁ && L.any fun t₂ => diffT t₀ t₂ && (diffT t₁ t₂ &&
        (memT v₂ t₂ && (verts t₂).any fun v₃ => v₃ != v₀ && (v₃ != v₁ && (v₃ != v₂ &&
          L.any fun t₃ => diffT t₀ t₃ && (diffT t₁ t₃ && (diffT t₂ t₃ &&
            (memT v₃ t₃ && (verts t₃).any fun v₄ => v₄ != v₀ && (v₄ != v₁ && (v₄ != v₂ &&
              (v₄ != v₃ && L.any fun t₄ => diffT t₀ t₄ && (diffT t₁ t₄ && (diffT t₂ t₄ &&
                (diffT t₃ t₄ && (memT v₄ t₄ && memT v₀ t₄))))))))))))))))

/-- The cycle search is complete: if it finds nothing, there is no Berge-`C₅`. -/
theorem not_containsBergeC5_of_cycleB {L : List (Triple n)} (h : cycleB L = false) :
    ¬ ContainsBergeC5 (ofTriples L) := by
  rintro ⟨v, e, hc⟩
  have ht : ∀ i, ∃ t ∈ L, t.toFinset = e i := fun i => mem_ofTriples.1 (hc.edges_mem i)
  choose t htL hte using ht
  have hv : ∀ i j, i ≠ j → v i ≠ v j := fun i j hij h => hij (hc.vertices_injective h)
  have hd : ∀ i j, i ≠ j → diffT (t i) (t j) = true := fun i j hij => by
    rw [diffT_iff, hte, hte]
    exact fun h => hij (hc.edges_injective h)
  have hl : ∀ i, v i ∈ (t i).toFinset := fun i => by rw [hte]; exact hc.left_mem i
  have hr : ∀ i, v (i + 1) ∈ (t i).toFinset := fun i => by rw [hte]; exact hc.right_mem i
  have hr4 : v 0 ∈ (t 4).toFinset := hr 4
  revert h
  simp only [cycleB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq, memT_iff,
    mem_verts, Bool.not_eq_false, imp_false]
  refine ⟨t 0, htL 0, v 0, hl 0, v 1, hr 0, (hv 1 0 (by decide)), t 1, htL 1,
    hd 0 1 (by decide), hl 1, v 2, hr 1, hv 2 0 (by decide), hv 2 1 (by decide), t 2, htL 2,
    hd 0 2 (by decide), hd 1 2 (by decide), hl 2, v 3, hr 2, hv 3 0 (by decide),
    hv 3 1 (by decide), hv 3 2 (by decide), t 3, htL 3, hd 0 3 (by decide), hd 1 3 (by decide),
    hd 2 3 (by decide), hl 3, v 4, hr 3, hv 4 0 (by decide), hv 4 1 (by decide),
    hv 4 2 (by decide), hv 4 3 (by decide), t 4, htL 4, hd 0 4 (by decide), hd 1 4 (by decide),
    hd 2 4 (by decide), hd 3 4 (by decide), hl 4, hr4⟩

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
four-edge path. -/
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
  · exact ⟨a, by simp, b, by simp, path4_of_pathB h1⟩
  · exact ⟨a, by simp, c, by simp, path4_of_pathB h1⟩
  · exact ⟨b, by simp, c, by simp, path4_of_pathB h1⟩

/-- Every vertex other than `0` has a two-edge path to `0`. -/
def ReachCheck {n : ℕ} [NeZero n] (L : List (Triple n)) : Prop :=
  ∀ a : Fin n, a ≠ 0 → reach2B L 0 a = true

instance {n : ℕ} [NeZero n] (L : List (Triple n)) : Decidable (ReachCheck L) := by
  unfold ReachCheck
  infer_instance

/-- An explicit hypergraph passing the uniformity, cycle, saturation and root checks is a rooted
piece with root `0`. -/
theorem isRootedPiece_ofTriples {N : ℕ} {L : List (Triple (N + 1))} (hu : uniformB L = true)
    (hfree : ¬ ContainsBergeC5 (ofTriples L)) (hs : SatCheck L) (hr : ReachCheck L) :
    IsRootedPiece (ofTriples L) 0 :=
  ⟨isThreeUniform_of_uniformB hu, hfree, pathSaturated_of_satCheck hs,
    fun a ha => reach2_of_reach2B (hr a ha)⟩

/-- An explicit hypergraph passing the uniformity, cycle and saturation checks is
Berge-`C₅`-saturated. -/
theorem isBergeC5Saturated_ofTriples {L : List (Triple n)} (hu : uniformB L = true)
    (hfree : ¬ ContainsBergeC5 (ofTriples L)) (hs : SatCheck L) :
    IsBergeC5Saturated (ofTriples L) :=
  isBergeC5Saturated_of_pathSaturated (isThreeUniform_of_uniformB hu) hfree
    (pathSaturated_of_satCheck hs)

end BergeC5
