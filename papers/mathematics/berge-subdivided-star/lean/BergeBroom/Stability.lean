import BergeBroom.ComponentClasses
import BergeBroom.Exceptional
import BergeBroom.Arithmetic

/-! # Stability for actual saturated uniform hypergraphs -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Berge

open scoped BigOperators

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- A connected loose star with at least `a` spokes, stated directly using its hyperedges. -/
def IsLooseStar {r : ℕ} (a : ℕ) (H : UniformHypergraph V r) : Prop :=
  (incidenceGraph H.edges).Connected ∧
    ∃ c : V, a ≤ H.edges.card ∧ (∀ e ∈ H.edges, c ∈ e) ∧
      ∀ v, v ≠ c → degree H.edges v ≤ 1

instance isLooseStarDecidable {r : ℕ} (a : ℕ) (H : UniformHypergraph V r) :
    Decidable (IsLooseStar a H) := Classical.propDecidable _

theorem IsLooseStar.isTree {r a : ℕ} {H : UniformHypergraph V r}
    (h : IsLooseStar a H) (ha : 1 ≤ a) (hr : 1 ≤ r) :
    (incidenceGraph H.edges).IsTree := by
  obtain ⟨hc, c, hm, hcone, hother⟩ := h
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < H.edges.card by omega)
  have hpos (v : V) : 0 < degree H.edges v := by
    by_contra hn
    have hd : degree H.edges v = 0 := by omega
    have heq := reachable_eq_of_degree_zero (incidenceGraph H.edges)
      (show (incidenceGraph H.edges).degree (.inl v) = 0 by simpa using hd)
      (hc (.inl v) (.inr ⟨e, he⟩))
    cases heq
  have hd : degree H.edges c = H.edges.card := by
    simp only [degree, incidentEdges, Finset.filter_eq_self.mpr hcone]
  have ho (v : V) (hv : v ≠ c) : degree H.edges v = 1 := by
    have := hother v hv
    have := hpos v
    omega
  have hesum : ∑ v ∈ (Finset.univ : Finset V).erase c, degree H.edges v =
      ((Finset.univ : Finset V).erase c).card := by
    calc
      _ = ∑ _v ∈ (Finset.univ : Finset V).erase c, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact ho v (Finset.mem_erase.mp hv).1
      _ = _ := by simp
  have hsum := Finset.sum_erase_add (Finset.univ : Finset V)
    (fun v => degree H.edges v) (Finset.mem_univ c)
  rw [hesum, hd, sum_degrees H] at hsum
  have hcard := Finset.card_erase_add_one (Finset.mem_univ c)
  rw [Finset.card_univ] at hcard
  have hmul : r * H.edges.card = (r - 1) * H.edges.card + H.edges.card := by
    calc
      r * H.edges.card = ((r - 1) + 1) * H.edges.card := by rw [Nat.sub_add_cancel hr]
      _ = _ := by rw [add_mul, one_mul]
  exact (incidence_isTree_iff hr H).mpr ⟨hc, by omega⟩

theorem mem_largeTreeComponents_iff_looseStar {a r : ℕ} (H : UniformHypergraph V r)
    (ha : 3 ≤ a) (hr : 3 ≤ r) (hSat : Saturated a H) (c : Component H.edges) :
    c ∈ largeTreeComponents H ↔ IsLooseStar a (componentHypergraph H c) := by
  constructor
  · intro hc
    obtain ⟨ht, hm⟩ := (mem_largeTreeComponents H c).mp hc
    have hcsat := componentHypergraph_saturated (by omega) H hSat c
    obtain ⟨v, hv, hcone, hother⟩ := saturated_tree_is_loose
      (componentHypergraph H c) ha hr hcsat ht hm
    exact ⟨componentHypergraph_connected H c,
      v, hv.trans (degree_le_edge_card _ _), hcone, hother⟩
  · intro hc
    have ht := hc.isTree (by omega) (by omega)
    obtain ⟨_, v, hm, _, _⟩ := hc
    exact (mem_largeTreeComponents H c).mpr ⟨ht, by omega⟩

/-- Vertices remaining after removal of every incidence-tree component with at least two edges.
For saturated hypergraphs in the theorem's range, these removed components are loose stars
with at least `a` edges, by `saturated_tree_is_loose` and `saturated_tree_edges_ge`. -/
def remainderOrder {r : ℕ} (H : UniformHypergraph V r) : ℕ := by
  classical
  exact ∑ c ∈ Finset.univ.filter (fun c => c ∉ largeTreeComponents H),
    Fintype.card (ComponentVertex H.edges c)

theorem remainderOrder_eq_not_looseStar {a r : ℕ} (H : UniformHypergraph V r)
    (ha : 3 ≤ a) (hr : 3 ≤ r) (hSat : Saturated a H) :
    remainderOrder H =
      ∑ c ∈ Finset.univ.filter (fun c => ¬ IsLooseStar a (componentHypergraph H c)),
        Fintype.card (ComponentVertex H.edges c) := by
  classical
  unfold remainderOrder
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_largeTreeComponents_iff_looseStar H ha hr hSat c]

theorem remainder_mass_bound {r a : ℕ} (H : UniformHypergraph V r)
    (ha : 3 ≤ a) (hr : 3 ≤ r) (hSat : Saturated a H) :
    ((r - 1) * a + 1) * largeTreeCount H + remainderOrder H ≤ Fintype.card V := by
  classical
  have hpoint (c : Component H.edges) :
      ((r - 1) * a + 1) * (if c ∈ largeTreeComponents H then 1 else 0) +
        (if c ∈ largeTreeComponents H then 0 else Fintype.card (ComponentVertex H.edges c)) ≤
          Fintype.card (ComponentVertex H.edges c) := by
    by_cases hc : c ∈ largeTreeComponents H
    · simpa only [hc, ite_true, Nat.mul_one, Nat.add_zero] using
        largeTree_component_order H ha hr hSat c hc
    · simp [hc]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpoint c)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id,
    Finset.filter_mem_eq_inter, Finset.univ_inter, sum_component_vertex_card,
    largeTreeCount, remainderOrder, Finset.sum_filter, ite_not] using hsum

theorem exceptional_sum_bounds {a s : ℕ} (H : UniformHypergraph V (s + 1))
    (ha : 3 ≤ a) (hs : 2 ≤ s) (hSat : Saturated a H) :
    singleComponentCount H + zeroComponentCount H ≤ s ∧
      (0 < largeTreeCount H → singleComponentCount H + zeroComponentCount H ≤ s - 1) := by
  obtain ⟨he, hz, hdisj, hz'⟩ := saturated_exceptional_component_budgets H ha (by omega) hSat
  constructor
  · rcases hdisj with he0 | hz0 <;> omega
  · intro hh
    have hzz := hz' hh
    rcases hdisj with he0 | hz0 <;> omega

theorem remainder_weighted_bound {a s : ℕ} (H : UniformHypergraph V (s + 1))
    (ha : 3 ≤ a) (hs : 2 ≤ s) (hSat : Saturated a H)
    (hh : 0 < largeTreeCount H) :
    remainderOrder H + s * a * Fintype.card V ≤
      s * (s * a + 1) * H.edges.card + (s * a + 1) * (s - 1) := by
  have hmass := component_mass_bound H (by omega)
  have hlarge := remainder_mass_bound H ha (by omega) hSat
  have hsmall := (exceptional_sum_bounds H ha hs hSat).2 hh
  simp only [Nat.add_sub_cancel] at hmass hlarge
  have hn : Fintype.card V ≤ s * H.edges.card + largeTreeCount H + (s - 1) := by omega
  have hmul := Nat.mul_le_mul_left (s * a + 1) hn
  nlinarith

/-- The exact quotient/remainder construction stays strictly below the next continuous bound. -/
theorem upper_rounding_bound {a s n : ℕ} (hs : 1 ≤ s) :
    s * (s * a + 1) * upperValue a s n + (s * a + 1) * (s - 1) + 1 ≤
      s * a * n + s * (s * a + 1) := by
  let A := s * a + 1
  let q := n / A
  let t := n % A
  let d := t / s
  let eps := t % s
  have hA : 0 < A := by dsimp [A]; omega
  have hnq : A * q + t = n := Nat.div_add_mod n A
  have htd : s * d + eps = t := Nat.div_add_mod t s
  have hU : upperValue a s n = a * q + d := rfl
  have ht : t < A := Nat.mod_lt n hA
  have hrel : s * A * upperValue a s n + A * eps = s * a * n + t := by
    rw [hU, ← hnq, ← htd]
    dsimp [A]
    ring
  have hs' : s - 1 + 1 = s := by omega
  have hAs : A * (s - 1) + A = s * A := by nlinarith
  change s * A * upperValue a s n + A * (s - 1) + 1 ≤ s * a * n + s * A
  nlinarith [Nat.zero_le (A * eps)]

theorem near_minimum_has_large_tree {a s k : ℕ} (H : UniformHypergraph V (s + 1))
    (ha : 3 ≤ a) (hs : 2 ≤ s) (hSat : Saturated a H)
    (hn : (s * a + 1) * (s * (k + 1) + 1) ≤ Fintype.card V)
    (hm : H.edges.card ≤ upperValue a s (Fintype.card V) + k) :
    0 < largeTreeCount H := by
  let n := Fintype.card V
  let A := s * a + 1
  let q := n / A
  let t := n % A
  let d := t / s
  let eps := t % s
  have hA : 0 < A := by dsimp [A]; omega
  have hq : s * (k + 1) + 1 ≤ q := by
    exact (Nat.le_div_iff_mul_le hA).mpr (by simpa [A, n, Nat.mul_comm] using hn)
  have hnq : A * q + t = n := Nat.div_add_mod n A
  have htd : s * d + eps = t := Nat.div_add_mod t s
  have hU : upperValue a s n = a * q + d := rfl
  have hdecomp : n = s * upperValue a s n + q + eps := by
    rw [hU, ← hnq, ← htd]
    dsimp [A]
    ring
  have hmass := component_mass_bound H (by omega)
  simp only [Nat.add_sub_cancel] at hmass
  have hsmall := (exceptional_sum_bounds H ha hs hSat).1
  have hsm := Nat.mul_le_mul_left s hm
  by_contra hh
  have hh0 : largeTreeCount H = 0 := by omega
  change H.edges.card ≤ upperValue a s n + k at hm
  change s * H.edges.card ≤ s * (upperValue a s n + k) at hsm
  change n ≤ s * H.edges.card + largeTreeCount H +
    singleComponentCount H + zeroComponentCount H at hmass
  nlinarith

theorem saturated_near_minimum_stability {a s k : ℕ} (H : UniformHypergraph V (s + 1))
    (ha : 3 ≤ a) (hs : 2 ≤ s) (hSat : Saturated a H)
    (hn : (s * a + 1) * (s * (k + 1) + 1) ≤ Fintype.card V)
    (hm : H.edges.card ≤ upperValue a s (Fintype.card V) + k) :
    0 < largeTreeCount H ∧ remainderOrder H ≤ s * (s * a + 1) * (k + 1) - 1 := by
  have hh := near_minimum_has_large_tree H ha hs hSat hn hm
  refine ⟨hh, ?_⟩
  have hw := remainder_weighted_bound H ha hs hSat hh
  have hm' := Nat.mul_le_mul_left (s * (s * a + 1)) hm
  have hu := upper_rounding_bound (a := a) (s := s) (n := Fintype.card V) (by omega)
  have hR : remainderOrder H + 1 ≤ s * (s * a + 1) * (k + 1) := by nlinarith
  omega

theorem saturated_minimum_remainder {a s : ℕ} (H : UniformHypergraph V (s + 1))
    (ha : 3 ≤ a) (hs : 2 ≤ s) (hSat : Saturated a H)
    (hn : (s * a + 1) * (s + 1) ≤ Fintype.card V)
    (hm : H.edges.card = upperValue a s (Fintype.card V)) :
    remainderOrder H ≤ s * (s * a + 1) - 1 := by
  have h := saturated_near_minimum_stability (k := 0) H ha hs hSat
    (by simpa using hn) (by omega)
  simpa using h.2

end Berge
