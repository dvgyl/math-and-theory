import CriticalHardcore.ComputationTree
import CriticalHardcore.WeightedPaths

namespace CriticalHardcore

variable {V : Type*} [DecidableEq V]

theorem computationTree_properlyLabeled (G : SimpleGraph V) (lam : ℝ)
    (k : ℕ) (S : Finset V) (u : V) (hu : u ∈ S) :
    WeightedTree.ProperlyLabeled G S (computationTree G lam k S u) := by
  induction k generalizing S u with
  | zero =>
      exact WeightedTree.ProperlyLabeled.node hu (by simp) (by simp) (by simp)
  | succ k ih =>
      apply WeightedTree.ProperlyLabeled.node hu
      · simpa only [List.map_map, Function.comp_def, computationTree_label,
          neighborStates, deletionStates_labels] using neighborList_nodup G S u
      · intro t ht
        obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp ht
        simpa using neighborState_adj G htv
      · intro t ht
        obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp ht
        exact (ih tv.1 tv.2 (neighborState_valid G htv)).mono (neighborState_subset G htv)

end CriticalHardcore
