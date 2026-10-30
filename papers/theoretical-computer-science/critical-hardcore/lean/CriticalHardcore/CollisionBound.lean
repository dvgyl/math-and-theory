import CriticalHardcore.NonbacktrackingTrials
import CriticalHardcore.CollisionScale

/-! The actual regular-graph survival estimate at the square-root scale. -/

open scoped BigOperators

namespace CriticalHardcore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All finite square-root survival sums are bounded uniformly. The graph,
its regularity, and the starting edge are the only walk assumptions. -/
theorem regular_survival_sqrt_sum_le_scale
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) (regular : G.IsRegularOfDegree (d + 1))
    (a b : V) (hab : G.Adj a b) (K : ℕ) :
    (∑ j ∈ Finset.range K,
      Real.sqrt ((orientedCount G a b j : ℝ) / (d : ℝ) ^ j)) ≤
      (collisionScale d (Fintype.card V) : ℝ) := by
  letI : NeZero d := ⟨by omega⟩
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  let L := frontierLength d (Fintype.card V)
  have hL : 1 ≤ L := frontierLength_pos hd hn
  have hpred : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hblock : 2 * (L - 1) + 1 = 2 * L - 1 := by omega
  let e : G.Dart := ⟨(a, b), hab⟩
  have hs := NBChoices.survival_sqrt_sum_le G regular e (L - 1) K
  have hs' : (∑ j ∈ Finset.range K,
      Real.sqrt ((orientedCount G a b j : ℝ) / (d : ℝ) ^ j)) ≤
      (((2 * L - 1) * (2 * Fintype.card V / d ^ (L - 1) + 4 * d ^ L) : ℕ) : ℝ) := by
    simpa only [NBChoices.survival, e, hpred, hblock] using hs
  exact hs'.trans (by exact_mod_cast collision_budget_le_scale hd hn)

end CriticalHardcore
