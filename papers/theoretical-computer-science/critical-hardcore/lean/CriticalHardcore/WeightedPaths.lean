import CriticalHardcore.WeightedTree
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
The structural link between a finite deletion computation tree and actual
self-avoiding paths of the original graph. Distinct paths are proved to be
distinct label lists; path multiplicities are not discarded without proof.
-/

set_option autoImplicit false

namespace CriticalHardcore
namespace WeightedTree

variable {V : Type*} [DecidableEq V]

/-- Children use distinct adjacent labels, and descendants cannot reuse a root label. -/
inductive ProperlyLabeled (G : SimpleGraph V) : Finset V → WeightedTree V → Prop where
  | node {S : Finset V} {u : V} {p : ℝ} {cs : List (WeightedTree V)}
      (root_mem : u ∈ S)
      (labels_nodup : (cs.map label).Nodup)
      (adjacent : ∀ c ∈ cs, G.Adj u c.label)
      (descendants : ∀ c ∈ cs, ProperlyLabeled G (S.erase u) c) :
      ProperlyLabeled G S (.node u p cs)

namespace ProperlyLabeled

variable {G : SimpleGraph V} {S T : Finset V} {t : WeightedTree V}

theorem root_mem (h : ProperlyLabeled G S t) : t.label ∈ S := by
  cases h with
  | node hu _ _ _ => exact hu

theorem labels_nodup (h : ProperlyLabeled G S t) : (t.children.map label).Nodup := by
  cases h with
  | node _ hn _ _ => exact hn

theorem adjacent (h : ProperlyLabeled G S t) {c : WeightedTree V} (hc : c ∈ t.children) :
    G.Adj t.label c.label := by
  cases h with
  | node _ _ ha _ => exact ha c hc

theorem child (h : ProperlyLabeled G S t) {c : WeightedTree V} (hc : c ∈ t.children) :
    ProperlyLabeled G (S.erase t.label) c := by
  cases h with
  | node _ _ _ hall => exact hall c hc

theorem mono (h : ProperlyLabeled G S t) (hST : S ⊆ T) : ProperlyLabeled G T t := by
  induction h generalizing T with
  | @node S u p cs hu hn ha hc ih =>
      apply ProperlyLabeled.node (hST hu) hn ha
      intro c hcs
      apply ih c hcs
      intro v hv
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,
        hST (Finset.mem_erase.mp hv).2⟩

end ProperlyLabeled

theorem head_of_mem_paths {t : WeightedTree V} {k : ℕ} {p : List V}
    (hp : p ∈ paths t k) : p.head? = some t.label := by
  cases k with
  | zero =>
      simp only [paths, List.mem_singleton] at hp
      subst p
      rfl
  | succ k =>
      simp only [paths, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨c, _, q, _, rfl⟩ := hp
      rfl

theorem mem_of_mem_paths {G : SimpleGraph V} {S : Finset V} {t : WeightedTree V}
    (h : ProperlyLabeled G S t) {k : ℕ} {p : List V} (hp : p ∈ paths t k)
    {v : V} (hv : v ∈ p) : v ∈ S := by
  induction k generalizing S t p with
  | zero =>
      simp only [paths, List.mem_singleton] at hp
      subst p
      simp only [List.mem_singleton] at hv
      subst v
      exact h.root_mem
  | succ k ih =>
      simp only [paths, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨c, hc, q, hq, rfl⟩ := hp
      rcases List.mem_cons.mp hv with rfl | hv
      · exact h.root_mem
      · exact Finset.mem_of_mem_erase (ih (h.child hc) hq hv)

theorem nodup_of_mem_paths {G : SimpleGraph V} {S : Finset V} {t : WeightedTree V}
    (h : ProperlyLabeled G S t) {k : ℕ} {p : List V} (hp : p ∈ paths t k) : p.Nodup := by
  induction k generalizing S t p with
  | zero =>
      simp only [paths, List.mem_singleton] at hp
      subst p
      simp
  | succ k ih =>
      simp only [paths, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨c, hc, q, hq, rfl⟩ := hp
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        exact Finset.not_mem_erase _ _ (mem_of_mem_paths (h.child hc) hq hm)
      · exact ih (h.child hc) hq

theorem chain_of_mem_paths {G : SimpleGraph V} {S : Finset V} {t : WeightedTree V}
    (h : ProperlyLabeled G S t) {k : ℕ} {p : List V} (hp : p ∈ paths t k) :
    p.Chain' G.Adj := by
  induction k generalizing S t p with
  | zero =>
      simp only [paths, List.mem_singleton] at hp
      subst p
      simp
  | succ k ih =>
      simp only [paths, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨c, hc, q, hq, rfl⟩ := hp
      apply List.Chain'.cons' (ih (h.child hc) hq)
      intro v hv
      rw [head_of_mem_paths hq] at hv
      have hv' : v = c.label := (Option.mem_some_iff.mp hv).symm
      subst v
      exact h.adjacent hc

/-- No two tree nodes at a depth represent the same original-graph path. -/
theorem paths_nodup {G : SimpleGraph V} {S : Finset V} {t : WeightedTree V}
    (h : ProperlyLabeled G S t) (k : ℕ) : (paths t k).Nodup := by
  induction k generalizing S t with
  | zero => simp [paths]
  | succ k ih =>
      change (t.children.flatMap (fun c => (paths c k).map (t.label :: ·))).Nodup
      apply List.nodup_flatMap.mpr
      constructor
      · intro c hc
        apply List.Nodup.map _ (ih (h.child hc))
        intro p q hpq
        exact (List.cons.inj hpq).2
      · have hpair : t.children.Pairwise (fun a b => a.label ≠ b.label) := by
          simpa only [List.Nodup, List.pairwise_map] using h.labels_nodup
        apply hpair.imp_of_mem
        intro a b ha hb hne
        intro p hp hp'
        obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
        obtain ⟨r, hr, her⟩ := List.mem_map.mp hp'
        have hqr : q = r := (List.cons.inj (heq.trans her.symm)).2
        have hheads := congrArg List.head? hqr
        rw [head_of_mem_paths hq, head_of_mem_paths hr] at hheads
        exact hne (Option.some.inj hheads)

end WeightedTree
end CriticalHardcore
