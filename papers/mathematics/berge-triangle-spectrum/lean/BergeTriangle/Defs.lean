import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# Berge triangles in triple systems: definitions and paired products

A triple system on a vertex type `V` is a finite family of `3`-element vertex sets.
A Berge triangle consists of three distinct vertices `x, y, z` and three distinct edges
containing the pairs `xy`, `yz` and `zx`; copies are not required to be induced.
A system is saturated when it is Berge-triangle-free and adding any absent triple
creates a Berge triangle.  A paired product has disjoint two-element pairs and a base;
its edges are all sets `P ∪ {b}`.
-/

namespace BergeTriangle

open Finset

section General

variable {V : Type*} [DecidableEq V]

/-- Every edge has exactly three vertices. -/
def IsThreeUniform (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- `H` contains a Berge triangle: distinct vertices `x, y, z` and distinct edges
`h₁ ⊇ {x, y}`, `h₂ ⊇ {y, z}`, `h₃ ⊇ {z, x}`. -/
def HasBergeTriangle (H : Finset (Finset V)) : Prop :=
  ∃ x y z : V, ∃ h₁ h₂ h₃ : Finset V,
    h₁ ∈ H ∧ h₂ ∈ H ∧ h₃ ∈ H ∧
    x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ h₁ ≠ h₂ ∧ h₂ ≠ h₃ ∧ h₃ ≠ h₁ ∧
    x ∈ h₁ ∧ y ∈ h₁ ∧ y ∈ h₂ ∧ z ∈ h₂ ∧ z ∈ h₃ ∧ x ∈ h₃

/-- `H` contains no Berge triangle. -/
def BergeTriangleFree (H : Finset (Finset V)) : Prop :=
  ¬ HasBergeTriangle H

/-- Berge-triangle saturation: a free triple system in which the addition of every absent
`3`-element set creates a Berge triangle.  The vertex set is all of `V`. -/
def IsSaturated (H : Finset (Finset V)) : Prop :=
  IsThreeUniform H ∧ BergeTriangleFree H ∧
    ∀ T : Finset V, T.card = 3 → T ∉ H → HasBergeTriangle (insert T H)

omit [DecidableEq V] in
theorem HasBergeTriangle.mono {H H' : Finset (Finset V)} (h : HasBergeTriangle H)
    (hHH' : H ⊆ H') : HasBergeTriangle H' := by
  obtain ⟨x, y, z, h₁, h₂, h₃, m₁, m₂, m₃, rest⟩ := h
  exact ⟨x, y, z, h₁, h₂, h₃, hHH' m₁, hHH' m₂, hHH' m₃, rest⟩

omit [DecidableEq V] in
theorem BergeTriangleFree.anti {H H' : Finset (Finset V)} (h : BergeTriangleFree H')
    (hHH' : H ⊆ H') : BergeTriangleFree H :=
  fun ht => h (ht.mono hHH')

/-- Closing a two-edge Berge path `a – w – b` by a new triple containing `a` and `b`. -/
theorem hasBergeTriangle_insert_of_path {H : Finset (Finset V)} {T h₁ h₂ : Finset V}
    {a b w : V} (hT : T ∉ H) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (hwa : w ≠ a)
    (hwb : w ≠ b) (h₁H : h₁ ∈ H) (h₂H : h₂ ∈ H) (h₁₂ : h₁ ≠ h₂)
    (ha₁ : a ∈ h₁) (hw₁ : w ∈ h₁) (hw₂ : w ∈ h₂) (hb₂ : b ∈ h₂) :
    HasBergeTriangle (insert T H) := by
  refine ⟨a, w, b, h₁, h₂, T, mem_insert_of_mem h₁H, mem_insert_of_mem h₂H,
    mem_insert_self _ _, hwa.symm, hwb, hab.symm, h₁₂, ?_, ?_, ha₁, hw₁, hw₂, hb₂, hb, ha⟩
  · rintro rfl
    exact hT h₂H
  · rintro rfl
    exact hT h₁H

omit [DecidableEq V] in
theorem ne_of_mem_of_not_mem' {e f : Finset V} {v : V} (hv : v ∈ e) (hv' : v ∉ f) : e ≠ f := by
  rintro rfl
  exact hv' hv

/-- Three distinct elements do not fit into a two-element set. -/
theorem three_not_mem_card_two {P : Finset V} (hP : P.card = 2) {x y z : V} (hx : x ∈ P)
    (hy : y ∈ P) (hz : z ∈ P) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) : False := by
  have h3 : ({x, y, z} : Finset V).card = 3 :=
    card_eq_three.2 ⟨x, y, z, hxy, hzx.symm, hyz, rfl⟩
  have hsub : ({x, y, z} : Finset V) ⊆ P := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have := card_le_card hsub
  omega

/-- Disjoint two-element pairs and a disjoint base.  The associated triple system has one
edge `insert b P` for every pair `P` and base vertex `b`. -/
structure PairSystem (V : Type*) [DecidableEq V] where
  pairs : Finset (Finset V)
  base : Finset V
  card_pair : ∀ P ∈ pairs, P.card = 2
  pairs_disjoint : ∀ P ∈ pairs, ∀ Q ∈ pairs, P ≠ Q → Disjoint P Q
  pair_base_disjoint : ∀ P ∈ pairs, Disjoint P base

namespace PairSystem

variable (S : PairSystem V)

/-- The edges `P ∪ {b}` of a pair system. -/
def edges : Finset (Finset V) :=
  (S.pairs ×ˢ S.base).image fun x => insert x.2 x.1

theorem mem_edges {T : Finset V} :
    T ∈ S.edges ↔ ∃ P ∈ S.pairs, ∃ b ∈ S.base, insert b P = T := by
  simp only [edges, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨P, b, ⟨hP, hb⟩, rfl⟩
    exact ⟨P, hP, b, hb, rfl⟩
  · rintro ⟨P, hP, b, hb, rfl⟩
    exact ⟨P, b, ⟨hP, hb⟩, rfl⟩

theorem insert_mem_edges {P : Finset V} {b : V} (hP : P ∈ S.pairs) (hb : b ∈ S.base) :
    insert b P ∈ S.edges :=
  S.mem_edges.2 ⟨P, hP, b, hb, rfl⟩

theorem not_mem_pair_of_mem_base {P : Finset V} (hP : P ∈ S.pairs) {v : V}
    (hv : v ∈ S.base) : v ∉ P :=
  fun h => disjoint_left.mp (S.pair_base_disjoint P hP) h hv

theorem eq_of_mem_of_mem {P Q : Finset V} (hP : P ∈ S.pairs) (hQ : Q ∈ S.pairs) {v : V}
    (hvP : v ∈ P) (hvQ : v ∈ Q) : P = Q := by
  by_contra hne
  exact disjoint_left.mp (S.pairs_disjoint P hP Q hQ hne) hvP hvQ

theorem eq_base_of_mem {P : Finset V} {b v : V} (hP : P ∈ S.pairs) (hv : v ∈ S.base)
    (h : v ∈ insert b P) : v = b := by
  rcases mem_insert.1 h with h | h
  · exact h
  · exact absurd h (S.not_mem_pair_of_mem_base hP hv)

theorem mem_pair_of_mem {P : Finset V} {b v : V} (hv : v ∉ S.base) (hb : b ∈ S.base)
    (h : v ∈ insert b P) : v ∈ P := by
  rcases mem_insert.1 h with h | h
  · subst h
    exact absurd hb hv
  · exact h

theorem card_edge {P : Finset V} {b : V} (hP : P ∈ S.pairs) (hb : b ∈ S.base) :
    (insert b P).card = 3 := by
  rw [card_insert_of_notMem (S.not_mem_pair_of_mem_base hP hb), S.card_pair P hP]

theorem isThreeUniform : IsThreeUniform S.edges := by
  intro e he
  obtain ⟨P, hP, b, hb, rfl⟩ := S.mem_edges.1 he
  exact S.card_edge hP hb

/-- The number of edges is the number of pairs times the size of the base. -/
theorem card_edges : S.edges.card = S.pairs.card * S.base.card := by
  rw [edges, card_image_of_injOn, card_product]
  rintro ⟨P, b⟩ hx ⟨Q, c⟩ hy h
  simp only [coe_product, Set.mem_prod, mem_coe] at hx hy h
  have hbc : b = c := S.eq_base_of_mem hy.1 hx.2 (by rw [← h]; exact mem_insert_self b P)
  subst hbc
  have hPQ : P = Q :=
    calc P = (insert b P).erase b := (erase_insert (S.not_mem_pair_of_mem_base hx.1 hx.2)).symm
      _ = (insert b Q).erase b := by rw [h]
      _ = Q := erase_insert (S.not_mem_pair_of_mem_base hy.1 hx.2)
  rw [hPQ]

/-- Pair systems are Berge-triangle-free. -/
theorem free : BergeTriangleFree S.edges := by
  rintro ⟨x, y, z, h₁, h₂, h₃, m₁, m₂, m₃, hxy, hyz, hzx, h₁₂, h₂₃, h₃₁,
    hx₁, hy₁, hy₂, hz₂, hz₃, hx₃⟩
  have two_base : ∀ {u v : V} {e : Finset V}, e ∈ S.edges → u ∈ S.base → v ∈ S.base →
      u ∈ e → v ∈ e → u = v := by
    intro u v e he hu hv hue hve
    obtain ⟨P, hP, b, hb, rfl⟩ := S.mem_edges.1 he
    rw [S.eq_base_of_mem hP hu hue, S.eq_base_of_mem hP hv hve]
  have one_base : ∀ {x y z : V} {h₁ h₂ h₃ : Finset V}, h₁ ∈ S.edges → h₂ ∈ S.edges →
      h₃ ∈ S.edges → h₂ ≠ h₃ → x ∈ h₁ → y ∈ h₁ → y ∈ h₂ → z ∈ h₂ → z ∈ h₃ → x ∈ h₃ →
      z ∈ S.base → x ∉ S.base → y ∉ S.base → False := by
    intro x y z h₁ h₂ h₃ m₁ m₂ m₃ h₂₃ hx₁ hy₁ hy₂ hz₂ hz₃ hx₃ hz hx hy
    obtain ⟨P₁, hP₁, b₁, hb₁, rfl⟩ := S.mem_edges.1 m₁
    obtain ⟨P₂, hP₂, b₂, hb₂, rfl⟩ := S.mem_edges.1 m₂
    obtain ⟨P₃, hP₃, b₃, hb₃, rfl⟩ := S.mem_edges.1 m₃
    have e₂ : z = b₂ := S.eq_base_of_mem hP₂ hz hz₂
    have e₃ : z = b₃ := S.eq_base_of_mem hP₃ hz hz₃
    have p₂ : P₂ = P₁ := S.eq_of_mem_of_mem hP₂ hP₁ (S.mem_pair_of_mem hy hb₂ hy₂)
      (S.mem_pair_of_mem hy hb₁ hy₁)
    have p₃ : P₃ = P₁ := S.eq_of_mem_of_mem hP₃ hP₁ (S.mem_pair_of_mem hx hb₃ hx₃)
      (S.mem_pair_of_mem hx hb₁ hx₁)
    apply h₂₃
    rw [← e₂, ← e₃, p₂, p₃]
  by_cases hx : x ∈ S.base <;> by_cases hy : y ∈ S.base <;> by_cases hz : z ∈ S.base
  · exact hxy (two_base m₁ hx hy hx₁ hy₁)
  · exact hxy (two_base m₁ hx hy hx₁ hy₁)
  · exact hzx (two_base m₃ hz hx hz₃ hx₃)
  · exact one_base m₂ m₃ m₁ h₃₁ hy₂ hz₂ hz₃ hx₃ hx₁ hy₁ hx hy hz
  · exact hyz (two_base m₂ hy hz hy₂ hz₂)
  · exact one_base m₃ m₁ m₂ h₁₂ hz₃ hx₃ hx₁ hy₁ hy₂ hz₂ hy hz hx
  · exact one_base m₁ m₂ m₃ h₂₃ hx₁ hy₁ hy₂ hz₂ hz₃ hx₃ hz hx hy
  · obtain ⟨P₁, hP₁, b₁, hb₁, rfl⟩ := S.mem_edges.1 m₁
    obtain ⟨P₂, hP₂, b₂, hb₂, rfl⟩ := S.mem_edges.1 m₂
    obtain ⟨P₃, hP₃, b₃, hb₃, rfl⟩ := S.mem_edges.1 m₃
    have hy1 := S.mem_pair_of_mem hy hb₁ hy₁
    have hx1 := S.mem_pair_of_mem hx hb₁ hx₁
    have p₂ : P₂ = P₁ := S.eq_of_mem_of_mem hP₂ hP₁ (S.mem_pair_of_mem hy hb₂ hy₂) hy1
    have hz1 : z ∈ P₁ := p₂ ▸ S.mem_pair_of_mem hz hb₂ hz₂
    exact three_not_mem_card_two (S.card_pair P₁ hP₁) hx1 hy1 hz1 hxy hyz hzx

/-- A triple outside a pair system whose vertices are covered contains two base vertices or
two vertices from different pairs. -/
theorem exists_split {T : Finset V} (hT3 : T.card = 3)
    (hcov : ∀ v ∈ T, v ∈ S.base ∨ ∃ P ∈ S.pairs, v ∈ P) (hT : T ∉ S.edges) :
    ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ ((a ∈ S.base ∧ b ∈ S.base) ∨
      ∃ P ∈ S.pairs, ∃ Q ∈ S.pairs, P ≠ Q ∧ a ∈ P ∧ b ∈ Q) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 hT3
  have ha : a ∈ ({a, b, c} : Finset V) := by simp
  have hb : b ∈ ({a, b, c} : Finset V) := by simp
  have hc : c ∈ ({a, b, c} : Finset V) := by simp
  -- if two covered vertices lie in one pair and the third is in the base, the triple is an edge
  have edge : ∀ {u v w : V} {P : Finset V}, P ∈ S.pairs → w ∈ S.base → u ∈ P → v ∈ P →
      u ≠ v → insert w {u, v} ∈ S.edges := by
    intro u v w P hP hw hu hv huv
    have hPuv : ({u, v} : Finset V) = P :=
      eq_of_subset_of_card_le (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption) (by rw [S.card_pair P hP, Finset.card_pair huv])
    rw [hPuv]
    exact S.insert_mem_edges hP hw
  rcases hcov a ha with haB | ⟨Pa, hPa, haP⟩ <;>
    rcases hcov b hb with hbB | ⟨Pb, hPb, hbP⟩ <;>
    rcases hcov c hc with hcB | ⟨Pc, hPc, hcP⟩
  · exact ⟨a, ha, b, hb, hab, Or.inl ⟨haB, hbB⟩⟩
  · exact ⟨a, ha, b, hb, hab, Or.inl ⟨haB, hbB⟩⟩
  · exact ⟨a, ha, c, hc, hac, Or.inl ⟨haB, hcB⟩⟩
  · by_cases hPQ : Pb = Pc
    · subst hPQ
      exact absurd (edge hPb haB hbP hcP hbc) hT
    · exact ⟨b, hb, c, hc, hbc, Or.inr ⟨Pb, hPb, Pc, hPc, hPQ, hbP, hcP⟩⟩
  · exact ⟨b, hb, c, hc, hbc, Or.inl ⟨hbB, hcB⟩⟩
  · by_cases hPQ : Pa = Pc
    · subst hPQ
      refine absurd ?_ hT
      have := edge hPa hbB haP hcP hac
      have e : (insert b {a, c} : Finset V) = {a, b, c} := by
        ext x
        simp only [mem_insert, mem_singleton]
        tauto
      rwa [e] at this
    · exact ⟨a, ha, c, hc, hac, Or.inr ⟨Pa, hPa, Pc, hPc, hPQ, haP, hcP⟩⟩
  · by_cases hPQ : Pa = Pb
    · subst hPQ
      refine absurd ?_ hT
      have := edge hPa hcB haP hbP hab
      have e : (insert c {a, b} : Finset V) = {a, b, c} := by
        ext x
        simp only [mem_insert, mem_singleton]
        tauto
      rwa [e] at this
    · exact ⟨a, ha, b, hb, hab, Or.inr ⟨Pa, hPa, Pb, hPb, hPQ, haP, hbP⟩⟩
  · by_cases hPQ : Pa = Pb
    · subst hPQ
      by_cases hPR : Pa = Pc
      · subst hPR
        exact (three_not_mem_card_two (S.card_pair Pa hPa) haP hbP hcP hab hbc
          (Ne.symm hac)).elim
      · exact ⟨a, ha, c, hc, hac, Or.inr ⟨Pa, hPa, Pc, hPc, hPR, haP, hcP⟩⟩
    · exact ⟨a, ha, b, hb, hab, Or.inr ⟨Pa, hPa, Pb, hPb, hPQ, haP, hbP⟩⟩

/-- A pair system covering every vertex, with at least one pair and one base vertex, is
saturated. -/
theorem saturated (hcov : ∀ v : V, v ∈ S.base ∨ ∃ P ∈ S.pairs, v ∈ P)
    (hpairs : S.pairs.Nonempty) (hbase : S.base.Nonempty) : IsSaturated S.edges := by
  refine ⟨S.isThreeUniform, S.free, fun T hT3 hT => ?_⟩
  obtain ⟨a, ha, b, hb, hab, h⟩ := S.exists_split hT3 (fun v _ => hcov v) hT
  rcases h with ⟨haB, hbB⟩ | ⟨P, hP, Q, hQ, hPQ, haP, hbQ⟩
  · obtain ⟨P, hP⟩ := hpairs
    obtain ⟨w, hw⟩ : P.Nonempty := card_pos.1 (by rw [S.card_pair P hP]; norm_num)
    refine hasBergeTriangle_insert_of_path hT ha hb hab ?_ ?_ (S.insert_mem_edges hP haB)
      (S.insert_mem_edges hP hbB) ?_ (mem_insert_self a P) (mem_insert_of_mem hw)
      (mem_insert_of_mem hw) (mem_insert_self b P)
    · rintro rfl
      exact S.not_mem_pair_of_mem_base hP haB hw
    · rintro rfl
      exact S.not_mem_pair_of_mem_base hP hbB hw
    · intro h
      exact hab (S.eq_base_of_mem hP haB (by rw [← h]; exact mem_insert_self a P))
  · obtain ⟨c, hc⟩ := hbase
    refine hasBergeTriangle_insert_of_path hT ha hb hab ?_ ?_ (S.insert_mem_edges hP hc)
      (S.insert_mem_edges hQ hc) ?_ (mem_insert_of_mem haP) (mem_insert_self c P)
      (mem_insert_self c Q) (mem_insert_of_mem hbQ)
    · rintro rfl
      exact S.not_mem_pair_of_mem_base hP hc haP
    · rintro rfl
      exact S.not_mem_pair_of_mem_base hQ hc hbQ
    · intro h
      apply hPQ
      have haQ : a ∈ insert c Q := by rw [← h]; exact mem_insert_of_mem haP
      exact S.eq_of_mem_of_mem hP hQ haP
        (S.mem_pair_of_mem (fun haB => S.not_mem_pair_of_mem_base hP haB haP) hc haQ)

/-- A covering pair system on a finite vertex type has `2 · #pairs + #base` vertices. -/
theorem two_mul_card_pairs_add_card_base [Fintype V]
    (hcov : ∀ v : V, v ∈ S.base ∨ ∃ P ∈ S.pairs, v ∈ P) :
    2 * S.pairs.card + S.base.card = Fintype.card V := by
  have hunion : S.pairs.biUnion id ∪ S.base = univ := by
    ext v
    simp only [mem_union, mem_biUnion, id, mem_univ, iff_true]
    rcases hcov v with h | ⟨P, hP, hv⟩
    · exact Or.inr h
    · exact Or.inl ⟨P, hP, hv⟩
  have hdisj : Disjoint (S.pairs.biUnion id) S.base := by
    rw [disjoint_biUnion_left]
    intro P hP
    exact S.pair_base_disjoint P hP
  have hcard : (S.pairs.biUnion id).card = 2 * S.pairs.card := by
    rw [card_biUnion]
    · rw [sum_const_nat (m := 2) (fun P hP => by simpa using S.card_pair P hP), mul_comm]
    · intro P hP Q hQ hPQ
      exact S.pairs_disjoint P hP Q hQ hPQ
  rw [← card_univ, ← hunion, card_union_of_disjoint hdisj, hcard]

end PairSystem

/-- A paired product: a pair system whose pairs and base partition the whole vertex set, with
at least one pair and at least one base vertex.  On `Fin n` these are exactly the systems
isomorphic to `F(n,p)` for some `1 ≤ p < n/2`. -/
structure PairedProduct (V : Type*) [DecidableEq V] extends PairSystem V where
  cover : ∀ v : V, v ∈ base ∨ ∃ P ∈ pairs, v ∈ P
  pairs_nonempty : pairs.Nonempty
  base_nonempty : base.Nonempty

/-- `H` is (isomorphic to) a paired product `F(n,p)`. -/
def IsPairedProduct (H : Finset (Finset V)) : Prop :=
  ∃ S : PairedProduct V, S.edges = H

/-- Every paired product is Berge-triangle saturated. -/
theorem PairedProduct.saturated (S : PairedProduct V) : IsSaturated S.edges :=
  S.toPairSystem.saturated S.cover S.pairs_nonempty S.base_nonempty

end General

/-! ## The numerical thresholds -/

/-- Győri's maximum `⌊n²/8⌋`. -/
def E (n : ℕ) : ℕ := n ^ 2 / 8

/-- The threshold `Lₙ = ⌊(n-1)²/8⌋`. -/
def L (n : ℕ) : ℕ := (n - 1) ^ 2 / 8

/-- The width `Wₙ = Eₙ - Lₙ` of the upper window. -/
def W (n : ℕ) : ℕ := E n - L n

/-- `m = p(n-2p)` for some `1 ≤ p < n/2`: the size of a paired product `F(n,p)`. -/
def IsProductSize (n m : ℕ) : Prop :=
  ∃ p, 1 ≤ p ∧ 2 * p < n ∧ m = p * (n - 2 * p)

/-- `m` is in the Berge-triangle saturation spectrum of triple systems on `n` vertices. -/
def InSaturationSpectrum (n m : ℕ) : Prop :=
  ∃ H : Finset (Finset (Fin n)), IsSaturated H ∧ H.card = m

/-- The statement of the dense-containment theorem (Theorem 1 of the manuscript) at order `n`:
every Berge-triangle-free triple system on `Fin n` with more than `Lₙ` edges is a spanning
subsystem of a paired product.  It is the hypothesis of the conditional theorems in
`BergeTriangle.Spectrum`; it is not proved in Lean. -/
def DenseContainment (n : ℕ) : Prop :=
  ∀ H : Finset (Finset (Fin n)), IsThreeUniform H → BergeTriangleFree H → L n < H.card →
    ∃ S : PairedProduct (Fin n), H ⊆ S.edges

end BergeTriangle
