import CriticalHardcore.DeletionRecursion
import CriticalHardcore.WeightedTree
import CriticalHardcore.WeightedTotals
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
The actual hard-core graph computation tree obtained by successive neighbor
deletion. A cardinality-sized recursion depth is sufficient for the exact
finite-graph observable expansion; it is not an approximation assumption.
-/

namespace CriticalHardcore

variable {V : Type*} [DecidableEq V]

noncomputable def computationTree (G : SimpleGraph V) (lam : ℝ) :
    ℕ → Finset V → V → WeightedTree V
  | 0, S, u => .node u (occupation G lam S u) []
  | k + 1, S, u => .node u (occupation G lam S u)
      ((neighborStates G S u).map (fun tv => computationTree G lam k tv.1 tv.2))

@[simp] theorem computationTree_label (G : SimpleGraph V) (lam : ℝ)
    (k : ℕ) (S : Finset V) (u : V) : (computationTree G lam k S u).label = u := by
  cases k <;> rfl

@[simp] theorem computationTree_message (G : SimpleGraph V) (lam : ℝ)
    (k : ℕ) (S : Finset V) (u : V) :
    (computationTree G lam k S u).message = occupation G lam S u := by
  cases k <;> rfl

@[simp] theorem computationTree_children_zero (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) : (computationTree G lam 0 S u).children = [] := rfl

@[simp] theorem computationTree_children_succ (G : SimpleGraph V) (lam : ℝ)
    (k : ℕ) (S : Finset V) (u : V) :
    (computationTree G lam (k + 1) S u).children =
      (neighborStates G S u).map (fun tv => computationTree G lam k tv.1 tv.2) := rfl

theorem computationTree_children_length (G : SimpleGraph V) (lam : ℝ)
    (k : ℕ) (S : Finset V) (u : V) :
    (computationTree G lam (k + 1) S u).children.length = (neighborList G S u).length := by
  simp [neighborStates]

theorem computationTree_children_messages (G : SimpleGraph V) (lam : ℝ)
    (k : ℕ) (S : Finset V) (u : V) :
    ((computationTree G lam (k + 1) S u).children.map WeightedTree.message) =
      (neighborStates G S u).map (fun tv => occupation G lam tv.1 tv.2) := by
  simp

section FiniteGraph

variable [Fintype V]

theorem neighborList_length_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u : V) :
    (neighborList G S u).length ≤ G.degree u := by
  classical
  unfold neighborList
  rw [Finset.length_toList, Finset.filter_congr_decidable]
  change (S.filter (G.Adj u)).card ≤ (G.neighborFinset u).card
  apply Finset.card_le_card
  intro v hv
  exact (G.mem_neighborFinset u v).mpr (Finset.mem_filter.mp hv).2

theorem neighborList_length_add_one_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    {u w : V} (hw : w ∉ S) (hwu : G.Adj w u) :
    (neighborList G S u).length + 1 ≤ G.degree u := by
  classical
  let N := S.filter (G.Adj u)
  have hwN : w ∉ N := fun h => hw (Finset.mem_filter.mp h).1
  have hs : insert w N ⊆ G.neighborFinset u := by
    intro v hv
    rcases Finset.mem_insert.mp hv with h | hv
    · subst v
      exact (G.mem_neighborFinset u w).mpr (G.symm hwu)
    · exact (G.mem_neighborFinset u v).mpr (Finset.mem_filter.mp hv).2
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_not_mem hwN] at hc
  unfold neighborList
  rw [Finset.length_toList, Finset.filter_congr_decidable]
  exact hc

theorem computationTree_good (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    (hdegree : ∀ v : V, G.degree v ≤ d + 1)
    (k : ℕ) (S : Finset V) (u : V) (hu : u ∈ S)
    (hparent : ∃ w, w ∉ S ∧ G.Adj w u) :
    WeightedTree.Good (d : ℝ) (pmax lam) (computationTree G lam k S u) := by
  induction k generalizing S u with
  | zero =>
      apply WeightedTree.Good.node
      · exact le_of_lt (occupation_pos G hlam S u)
      · exact occupation_le_pmax G hlam hu
      · simp
      · simp
  | succ k ih =>
      obtain ⟨w, hw, hwu⟩ := hparent
      have hn : (neighborList G S u).length ≤ d := by
        have h1 := neighborList_length_add_one_le_degree G S hw hwu
        have h2 := hdegree u
        omega
      apply WeightedTree.Good.node
      · exact le_of_lt (occupation_pos G hlam S u)
      · exact occupation_le_pmax G hlam hu
      · simpa only [List.map_map, Function.comp_def, computationTree_message]
          using occupation_local_contraction G hlam d hd hcritical hu hn
      · intro t ht
        obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp ht
        apply ih tv.1 tv.2 (neighborState_valid G htv)
        refine ⟨u, ?_, neighborState_adj G htv⟩
        intro hut
        exact (Finset.mem_erase.mp (neighborState_subset G htv hut)).1 rfl

theorem computationTree_good_children (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    (hdegree : ∀ v : V, G.degree v ≤ d + 1)
    (k : ℕ) (S : Finset V) (u : V) :
    ∀ t ∈ (computationTree G lam k S u).children,
      WeightedTree.Good (d : ℝ) (pmax lam) t := by
  cases k with
  | zero => simp
  | succ k =>
      intro t ht
      obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp ht
      apply computationTree_good G hlam d hd hcritical hdegree k tv.1 tv.2
        (neighborState_valid G htv)
      refine ⟨u, ?_, neighborState_adj G htv⟩
      intro hut
      exact (Finset.mem_erase.mp (neighborState_subset G htv hut)).1 rfl

end FiniteGraph

private theorem abs_sum_map_le {A : Type*} (l : List A) (f : A → ℝ) :
    |(l.map f).sum| ≤ (l.map (fun a => |f a|)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add_left ih _)

private theorem sum_map_mono {A : Type*} (l : List A) (f g : A → ℝ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a List.mem_cons_self)
        (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- The exact finite Gibbs influence is bounded by the actual computation tree.
The depth hypothesis ensures that all deletion branches have terminated. -/
theorem observableInfluence_le_computationTree (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) (S : Finset V) (u : V) (hu : u ∈ S)
    (hdepth : S.card ≤ k) (f : V → ℝ) (hf : ∀ v ∈ S, |f v| ≤ 1) :
    |observableInfluence G lam S u f| ≤
      WeightedTree.truncatedTotal (computationTree G lam k S u) k := by
  induction k generalizing S u with
  | zero =>
      have hpos := Finset.card_pos.mpr ⟨u, hu⟩
      omega
  | succ k ih =>
      have hchild : ∀ tv ∈ neighborStates G S u,
          |observableInfluence G lam tv.1 tv.2 f| ≤
            WeightedTree.truncatedTotal (computationTree G lam k tv.1 tv.2) k := by
        intro tv htv
        apply ih tv.1 tv.2 (neighborState_valid G htv)
        · have := neighborState_card_lt G hu htv
          omega
        · intro v hv
          exact hf v (Finset.mem_of_mem_erase (neighborState_subset G htv hv))
      have hs := sum_map_mono (neighborStates G S u)
        (fun tv => |occupation G lam tv.1 tv.2 * observableInfluence G lam tv.1 tv.2 f|)
        (fun tv => occupation G lam tv.1 tv.2 *
          WeightedTree.truncatedTotal (computationTree G lam k tv.1 tv.2) k)
        (by
          intro tv htv
          dsimp only
          rw [abs_mul, abs_of_nonneg (le_of_lt (occupation_pos G hlam _ _))]
          exact mul_le_mul_of_nonneg_left (hchild tv htv)
            (le_of_lt (occupation_pos G hlam _ _)))
      rw [observableInfluence_recursion G hlam, WeightedTree.truncatedTotal_succ]
      simp only [computationTree_children_succ, List.map_map, Function.comp_def,
        computationTree_message]
      calc
        |f u - ((neighborStates G S u).map
            (fun tv => occupation G lam tv.1 tv.2 *
              observableInfluence G lam tv.1 tv.2 f)).sum| ≤
            |f u| + |((neighborStates G S u).map
              (fun tv => occupation G lam tv.1 tv.2 *
                observableInfluence G lam tv.1 tv.2 f)).sum| := abs_sub _ _
        _ ≤ 1 + ((neighborStates G S u).map
              (fun tv => |occupation G lam tv.1 tv.2 *
                observableInfluence G lam tv.1 tv.2 f|)).sum :=
          add_le_add (hf u hu) (abs_sum_map_le _ _)
        _ ≤ _ := add_le_add_left hs 1

end CriticalHardcore
