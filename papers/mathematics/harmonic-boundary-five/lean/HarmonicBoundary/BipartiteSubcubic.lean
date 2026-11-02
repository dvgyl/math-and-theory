import HarmonicBoundary.RootSectors

set_option linter.unusedSectionVars false

/-!
# Bipartite vertices of degree at most three

`BipartiteColor` is an actual two-coloring: colors are natural numbers and
the colors at the endpoints of every edge sum to one.  The distance table
is certified by `DistanceCertificate`, so no assumed distance identities
or boundary witnesses enter the result.

A cycle through `root` is certified by two different neighbors joined by
an actual walk avoiding `root`.  In a finite simple graph this is equivalent
to the usual simple-cycle formulation (erase repeated vertices in the
avoiding walk).  The main result below concerns exactly this witness.
-/

namespace HarmonicBoundary
namespace BipartiteSubcubic

open RootSectors

universe u
variable {V : Type u} {Adj : V → V → Prop} {D : V → V → Nat}
variable [DecidableRel Adj]

def BipartiteColor (Adj : V → V → Prop) (color : V → Nat) : Prop :=
  ∀ x y, Adj x y → color x + color y = 1

def CycleAt (Adj : V → V → Prop) (root : V) : Prop :=
  ∃ a b n, Adj root a ∧ Adj root b ∧ a ≠ b ∧
    WalkLen (AwayAdj Adj root) a b n

theorem same_length_color (color : V → Nat) (proper : BipartiteColor Adj color)
    {a b : V} {n : Nat} (p : WalkLen Adj a b n) :
    ∀ {c d}, WalkLen Adj c d n → color a = color c → color b = color d := by
  induction p with
  | nil a =>
    intro c d q h
    cases q
    exact h
  | @cons a a' b n haa p ih =>
    intro c d q h
    cases q with
    | @cons _ c' _ _ hcc q =>
      apply ih q
      have ha := proper a a' haa
      have hc := proper c c' hcc
      omega

theorem no_horizontal_edge (cert : DistanceCertificate Adj D)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {root x y : V} (hxy : Adj x y) : D root x ≠ D root y := by
  intro he
  have wx := certified_distance_realized cert root x
  have wy := certified_distance_realized cert root y
  rw [he] at wx
  have hc := same_length_color color proper wx wy rfl
  have hp := proper x y hxy
  omega

/-- Unique first steps in a bipartite graph separate every pair of root
neighbors, including when deletion of the root is disconnected already. -/
theorem unique_first_no_cycle (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) (loopless : ∀ x, ¬Adj x x)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {root : V} (uf : UniqueFirst Adj D root) : ¬CycleAt Adj root := by
  intro hc
  obtain ⟨a, b, n, ha, hb, hab, walk⟩ := hc
  have sa := neighbor_in_sector cert loopless ha
  have sb := neighbor_in_sector cert loopless hb
  have bn : ¬Sector Adj D root a b := by
    intro hs
    exact hab (sector_unique uf hs sb)
  obtain ⟨x, y, hx, hy, hxy, hxr, hyr⟩ :=
    walk_set_exit (Sector Adj D root a) walk sa bn
  have he := cross_outside_sector_level cert sym uf hx hyr hy hxy
  exact no_horizontal_edge cert color proper hxy he

theorem degree_three_cycle_boundary
    (vs : List V) (nodup : vs.Nodup) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) (loopless : ∀ x, ¬Adj x x)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {root a b c : V} (neighbors : ThreeNeighbors Adj root a b c)
    (cycle : CycleAt Adj root) : Boundary Adj D vs root := by
  classical
  by_cases hn : Boundary Adj D vs root
  · exact hn
  · have ni := three_nonboundary_inequality vs nodup complete neighbors hn
    have uf := three_nonboundary_unique_first cert sym neighbors ni
    exact False.elim (unique_first_no_cycle cert sym loopless color proper uf cycle)

def OneNeighbor (Adj : V → V → Prop) (root a : V) : Prop :=
  ∀ w, Adj root w ↔ w = a

def TwoNeighbors (Adj : V → V → Prop) (root a b : V) : Prop :=
  a ≠ b ∧ ∀ w, Adj root w ↔ w = a ∨ w = b

def SmallPositiveDegree (Adj : V → V → Prop) (root : V) : Prop :=
  (∃ a, OneNeighbor Adj root a) ∨
  (∃ a b, TwoNeighbors Adj root a b) ∨
  (∃ a b c, ThreeNeighbors Adj root a b c)

theorem one_neighbor_score (vs : List V) (nodup : vs.Nodup)
    (complete : ∀ x, x ∈ vs) {root a : V}
    (hn : OneNeighbor Adj root a) (t : V) :
    score Adj D vs root t = (D root t : Int) - (D a t : Int) := by
  classical
  have he : score Adj D vs root t =
      isum vs (fun x => if x = a then (D root t : Int) - (D a t : Int) else 0) := by
    apply isum_congr
    intro x hx
    by_cases h : x = a
    · subst x
      have ha := (hn a).mpr rfl
      simp [edgeScore, ha]
    · have ha : ¬Adj root x := fun he => h ((hn x).mp he)
      simp [edgeScore, ha, h]
  rw [he, isum_indicator vs nodup]
  simp only [complete, ite_true]

theorem leaf_boundary (vs : List V) (nodup : vs.Nodup)
    (complete : ∀ x, x ∈ vs) (cert : DistanceCertificate Adj D)
    (loopless : ∀ x, ¬Adj x x) {root a : V}
    (hn : OneNeighbor Adj root a) : Boundary Adj D vs root := by
  refine ⟨a, ?_⟩
  rw [one_neighbor_score vs nodup complete hn]
  have ha := adjacent_distance_one cert loopless ((hn a).mpr rfl)
  have hz := (cert.zeroIff a a).mpr rfl
  omega

theorem two_neighbor_score (vs : List V) (nodup : vs.Nodup)
    (complete : ∀ x, x ∈ vs) {root a b : V}
    (hn : TwoNeighbors Adj root a b) (t : V) :
    score Adj D vs root t =
      2 * (D root t : Int) - (D a t : Int) - (D b t : Int) := by
  classical
  let ka := (D root t : Int) - (D a t : Int)
  let kb := (D root t : Int) - (D b t : Int)
  have he : score Adj D vs root t =
      isum vs (fun x => (if x = a then ka else 0) + (if x = b then kb else 0)) := by
    apply isum_congr
    intro x hx
    by_cases hxa : x = a
    · subst x
      have ha := (hn.2 a).mpr (Or.inl rfl)
      simp [edgeScore, ha, hn.1, ka]
    · by_cases hxb : x = b
      · subst x
        have hb := (hn.2 b).mpr (Or.inr rfl)
        simp [edgeScore, hb, hxa, kb]
      · have hna : ¬Adj root x := by
          intro hh
          rcases (hn.2 x).mp hh with hh | hh
          · exact hxa hh
          · exact hxb hh
        simp [edgeScore, hna, hxa, hxb]
  rw [he, isum_add, isum_indicator vs nodup a ka, isum_indicator vs nodup b kb]
  simp only [complete, ite_true]
  dsimp only [ka, kb]
  omega

theorem two_nonboundary_unique_first
    (vs : List V) (nodup : vs.Nodup) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    {root a b : V} (hn : TwoNeighbors Adj root a b)
    (nb : ¬Boundary Adj D vs root) : UniqueFirst Adj D root := by
  intro x hxr
  have hp : 0 < D root x := by
    have hz : D root x ≠ 0 := by
      intro he
      exact hxr ((cert.zeroIff root x).mp he).symm
    omega
  obtain ⟨v, hv, hdv⟩ := cert.descent root x hp
  refine ⟨v, hv, hdv.symm, ?_⟩
  intro w hw hdw
  have hi : 2 * D root x ≤ D a x + D b x := by
    have hs : score Adj D vs root x ≤ 0 := by
      by_cases hh : 0 < score Adj D vs root x
      · exact False.elim (nb ⟨x, hh⟩)
      · omega
    rw [two_neighbor_score vs nodup complete hn] at hs
    omega
  rcases (hn.2 v).mp hv with hve | hve <;>
    rcases (hn.2 w).mp hw with hwe | hwe
  all_goals first | exact hwe.trans hve.symm | (simp only [hve, hwe] at hdv hdw; omega)

theorem degree_two_cycle_boundary
    (vs : List V) (nodup : vs.Nodup) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) (loopless : ∀ x, ¬Adj x x)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {root a b : V} (neighbors : TwoNeighbors Adj root a b)
    (cycle : CycleAt Adj root) : Boundary Adj D vs root := by
  classical
  by_cases hn : Boundary Adj D vs root
  · exact hn
  · have uf := two_nonboundary_unique_first vs nodup complete cert sym neighbors hn
    exact False.elim (unique_first_no_cycle cert sym loopless color proper uf cycle)

theorem walk_join {a b c : V} {m n : Nat}
    (p : WalkLen Adj a b m) (q : WalkLen Adj b c n) : WalkLen Adj a c (m + n) := by
  induction p with
  | nil v => simpa using q
  | cons hab p ih =>
    have h := WalkLen.cons hab (ih q)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem short_walk_avoids_root (cert : DistanceCertificate Adj D)
    {root a t : V} {n : Nat} (p : WalkLen Adj a t n)
    (hshort : n < D root t) : WalkLen (AwayAdj Adj root) a t n := by
  induction p with
  | nil v => exact WalkLen.nil v
  | @cons a b t n hab p ih =>
    have hb := certified_distance_lower_bound cert p
    have ha := certified_distance_lower_bound cert (WalkLen.cons hab p)
    have han : a ≠ root := by intro h; subst a; omega
    have hbn : b ≠ root := by intro h; subst b; omega
    exact WalkLen.cons ⟨hab, han, hbn⟩ (ih (by omega))

/-- Two shorter root-neighbor distances produce an actual cycle witness;
the construction joins certified geodesics without passing through root. -/
theorem two_closer_cycle (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) {root a b t : V}
    (ha : Adj root a) (hb : Adj root b) (hne : a ≠ b)
    (hda : D a t < D root t) (hdb : D b t < D root t) : CycleAt Adj root := by
  classical
  have wa := short_walk_avoids_root cert (certified_distance_realized cert a t) hda
  have wb := short_walk_avoids_root cert (certified_distance_realized cert b t) hdb
  have away_sym : ∀ x y, AwayAdj Adj root x y → AwayAdj Adj root y x := by
    intro x y h
    exact ⟨sym x y h.1, h.2.2, h.2.1⟩
  have wt := walk_reverse away_sym wb
  exact ⟨a, b, D a t + D b t, ha, hb, hne, walk_join wa wt⟩

theorem bipartite_edge_distance (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {x y t : V} (hxy : Adj x y) :
    D x t + 1 = D y t ∨ D y t + 1 = D x t := by
  have h1 := cert.edgeLipschitz x y t hxy
  have h2 := cert.edgeLipschitz y x t (sym x y hxy)
  have hn := no_horizontal_edge cert color proper (root := t) hxy
  rw [distance_symm cert sym t x, distance_symm cert sym t y] at hn
  omega

theorem degree_two_boundary_cycle
    (vs : List V) (nodup : vs.Nodup) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {root a b : V} (neighbors : TwoNeighbors Adj root a b)
    (boundary : Boundary Adj D vs root) : CycleAt Adj root := by
  obtain ⟨t, ht⟩ := boundary
  rw [two_neighbor_score vs nodup complete neighbors] at ht
  have ha := (neighbors.2 a).mpr (Or.inl rfl)
  have hb := (neighbors.2 b).mpr (Or.inr rfl)
  have hda := bipartite_edge_distance cert sym color proper (t := t) ha
  have hdb := bipartite_edge_distance cert sym color proper (t := t) hb
  exact two_closer_cycle cert sym (t := t) ha hb neighbors.1 (by omega) (by omega)

theorem degree_three_boundary_cycle
    (vs : List V) (nodup : vs.Nodup) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {root a b c : V} (neighbors : ThreeNeighbors Adj root a b c)
    (boundary : Boundary Adj D vs root) : CycleAt Adj root := by
  obtain ⟨t, ht⟩ := boundary
  rw [three_neighbor_score vs nodup complete neighbors] at ht
  have ha := (neighbors.2.2.2 a).mpr (Or.inl rfl)
  have hb := (neighbors.2.2.2 b).mpr (Or.inr (Or.inl rfl))
  have hc := (neighbors.2.2.2 c).mpr (Or.inr (Or.inr rfl))
  have hda := bipartite_edge_distance cert sym color proper (t := t) ha
  have hdb := bipartite_edge_distance cert sym color proper (t := t) hb
  have hdc := bipartite_edge_distance cert sym color proper (t := t) hc
  have hpair :
      (D a t < D root t ∧ D b t < D root t) ∨
      (D a t < D root t ∧ D c t < D root t) ∨
      (D b t < D root t ∧ D c t < D root t) := by omega
  rcases hpair with hab | hac | hbc
  · exact two_closer_cycle cert sym ha hb neighbors.1 hab.1 hab.2
  · exact two_closer_cycle cert sym ha hc neighbors.2.1 hac.1 hac.2
  · exact two_closer_cycle cert sym hb hc neighbors.2.2.1 hbc.1 hbc.2

/-- Main graph-level characterization. Exact adjacency and a certified
shortest-path metric are the only graph data. All degree-two and degree-three
cycle witnesses, including those through cutvertices, are covered. -/
theorem boundary_iff_leaf_or_cycle
    (vs : List V) (nodup : vs.Nodup) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) (loopless : ∀ x, ¬Adj x x)
    (color : V → Nat) (proper : BipartiteColor Adj color)
    {root : V} (degree : SmallPositiveDegree Adj root) :
    Boundary Adj D vs root ↔ (∃ a, OneNeighbor Adj root a) ∨ CycleAt Adj root := by
  constructor
  · intro hb
    rcases degree with h1 | h2 | h3
    · exact Or.inl h1
    · obtain ⟨a, b, hn⟩ := h2
      exact Or.inr (degree_two_boundary_cycle vs nodup complete cert sym color proper hn hb)
    · obtain ⟨a, b, c, hn⟩ := h3
      exact Or.inr (degree_three_boundary_cycle vs nodup complete cert sym color proper hn hb)
  · intro h
    rcases h with h1 | hc
    · obtain ⟨a, hn⟩ := h1
      exact leaf_boundary vs nodup complete cert loopless hn
    · rcases degree with h1 | h2 | h3
      · obtain ⟨a, hn⟩ := h1
        exact leaf_boundary vs nodup complete cert loopless hn
      · obtain ⟨a, b, hn⟩ := h2
        exact degree_two_cycle_boundary vs nodup complete cert sym loopless color proper hn hc
      · obtain ⟨a, b, c, hn⟩ := h3
        exact degree_three_cycle_boundary vs nodup complete cert sym loopless color proper hn hc

end BipartiteSubcubic
end HarmonicBoundary

#print axioms HarmonicBoundary.BipartiteSubcubic.degree_three_cycle_boundary
#print axioms HarmonicBoundary.BipartiteSubcubic.boundary_iff_leaf_or_cycle
