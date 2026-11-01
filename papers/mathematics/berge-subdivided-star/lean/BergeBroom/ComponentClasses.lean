import BergeBroom.Components
import BergeBroom.Lower
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
namespace Berge
open scoped BigOperators
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

def zeroComponentCount {r : ℕ} (H : UniformHypergraph V r) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c : Component H.edges =>
    (componentHypergraph H c).edges.card=0)).card

def singleComponentCount {r : ℕ} (H : UniformHypergraph V r) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c : Component H.edges =>
    (componentHypergraph H c).edges.card=1)).card

def largeTreeComponents {r : ℕ} (H : UniformHypergraph V r) : Finset (Component H.edges) := by
  classical
  exact Finset.univ.filter (fun c =>
    (incidenceGraph (componentHypergraph H c).edges).IsTree ∧
    2 ≤ (componentHypergraph H c).edges.card)

def largeTreeCount {r : ℕ} (H : UniformHypergraph V r) : ℕ := (largeTreeComponents H).card

@[simp] theorem mem_largeTreeComponents {r : ℕ} (H : UniformHypergraph V r)
    (c : Component H.edges) :
    c ∈ largeTreeComponents H ↔
      (incidenceGraph (componentHypergraph H c).edges).IsTree ∧
      2 ≤ (componentHypergraph H c).edges.card := by
  classical
  simp [largeTreeComponents]

theorem component_mass_bound {r : ℕ} (H : UniformHypergraph V r) (hr : 1 ≤ r) :
    Fintype.card V ≤ (r-1)*H.edges.card + largeTreeCount H +
      singleComponentCount H + zeroComponentCount H := by
  classical
  have hpoint (c : Component H.edges) :
      Fintype.card (ComponentVertex H.edges c) ≤
        (r-1)*(componentHypergraph H c).edges.card +
        (if c ∈ largeTreeComponents H then 1 else 0) +
        (if (componentHypergraph H c).edges.card=1 then 1 else 0) +
        (if (componentHypergraph H c).edges.card=0 then 1 else 0) := by
    have hb := component_vertex_bound hr H c
    by_cases h0 : (componentHypergraph H c).edges.card=0
    · rw [ite_eq_left h0]
      omega
    by_cases h1 : (componentHypergraph H c).edges.card=1
    · rw [ite_eq_left h1]
      omega
    by_cases ht : (incidenceGraph (componentHypergraph H c).edges).IsTree
    · have hm : 2 ≤ (componentHypergraph H c).edges.card := by omega
      have hc := (mem_largeTreeComponents H c).mpr ⟨ht,hm⟩
      simp only [hc, ite_true, h1, h0, ite_false, Nat.add_zero]
      exact hb
    · have hc : c ∉ largeTreeComponents H := fun hc => ht ((mem_largeTreeComponents H c).mp hc).1
      simp only [hc, ite_false, h1, h0, Nat.add_zero]
      exact connected_not_tree_vertex_bound hr (componentHypergraph H c)
        (componentHypergraph_connected H c) ht
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpoint c)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_component_vertex_card, sum_componentHypergraph_edge_card,
    Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.univ_inter,
    largeTreeCount, singleComponentCount, zeroComponentCount] using hs

theorem largeTree_component_order {r a : ℕ} (H : UniformHypergraph V r)
    (ha : 3 ≤ a) (hr : 3 ≤ r) (hSat : Saturated a H)
    (c : Component H.edges) (hc : c ∈ largeTreeComponents H) :
    (r-1)*a+1 ≤ Fintype.card (ComponentVertex H.edges c) := by
  obtain ⟨ht,hm⟩ := (mem_largeTreeComponents H c).mp hc
  have hcsat := componentHypergraph_saturated (by omega) H hSat c
  have he := saturated_tree_edges_ge (componentHypergraph H c) ha hr hcsat ht hm
  have hv := ((incidence_isTree_iff (by omega) (componentHypergraph H c)).mp ht).2
  rw [hv]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ he) 1

theorem largeTree_mass_bound {r a : ℕ} (H : UniformHypergraph V r)
    (ha : 3 ≤ a) (hr : 3 ≤ r) (hSat : Saturated a H) :
    ((r-1)*a+1)*largeTreeCount H ≤ Fintype.card V := by
  classical
  have hpoint (c : Component H.edges) :
      ((r-1)*a+1)*(if c ∈ largeTreeComponents H then 1 else 0) ≤
        Fintype.card (ComponentVertex H.edges c) := by
    by_cases hc : c ∈ largeTreeComponents H
    · simpa only [hc, ite_true, Nat.mul_one] using largeTree_component_order H ha hr hSat c hc
    · simp [hc]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpoint c)
  simpa only [← Finset.mul_sum, Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter,
    Finset.univ_inter, sum_component_vertex_card, largeTreeCount] using hs

end Berge
