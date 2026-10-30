import CriticalHardcore.ComputationGeometry
import CriticalHardcore.PathCountBridge
import CriticalHardcore.GibbsInfluence
import Mathlib.Data.Real.Sqrt

/-!
Transfer from actual nonbacktracking self-avoidance counts to actual finite
hard-core Gibbs influences. The remaining walk-count estimate is isolated as
a hypothesis here and is discharged by the graph collision theorem in the
final result. This intermediate theorem alone is not the research claim.
-/

open scoped BigOperators

namespace CriticalHardcore

variable {V W : Type*} [DecidableEq V] [Fintype W]

namespace WeightedTree

theorem mass_le_sqrt_orientedCount {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ↪g H) {S : Finset V} {t : WeightedTree V} {u : V}
    {d pmax : ℝ} (hd : 0 < d) (hpmax : 0 ≤ pmax)
    (hg : Good d pmax t) (hl : ProperlyLabeled G S t)
    (hu : u ∉ S) (ha : G.Adj u t.label) (k : ℕ) :
    mass t k ≤ pmax * Real.sqrt ((orientedCount H (e u) (e t.label) k : ℝ) / d ^ k) := by
  have hc : (count t k : ℝ) ≤ (orientedCount H (e u) (e t.label) k : ℝ) := by
    exact_mod_cast count_le_orientedCount e hl hu ha k
  have hs : mass t k ^ 2 ≤ pmax ^ 2 *
      ((orientedCount H (e u) (e t.label) k : ℝ) / d ^ k) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hd k)).mpr
    exact (mass_sq_scaled_le hd.le hg k).trans
      (mul_le_mul_of_nonneg_left hc (sq_nonneg pmax))
  have h := Real.le_sqrt_of_sq_le hs
  rwa [Real.sqrt_mul (sq_nonneg pmax), Real.sqrt_sq hpmax] at h

end WeightedTree

private theorem sum_range_map_swap {A : Type*} (l : List A) (f : A → ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, (l.map (fun a => f a j)).sum) =
      (l.map (fun a => ∑ j ∈ Finset.range k, f a j)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

variable [Fintype V]

/-- Uniform finite square-root survival sums control the actual influence
under every induced free-vertex restriction. No SAW identity is assumed. -/
theorem computationTree_bound_from_walks
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) (e : G ↪g H)
    {lam B : ℝ} (hlam : 0 < lam) (hB : 0 ≤ B)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    (hdegree : ∀ v : V, G.degree v ≤ d + 1)
    (hwalks : ∀ a b : W, H.Adj a b → ∀ K : ℕ,
      (∑ j ∈ Finset.range K,
        Real.sqrt ((orientedCount H a b j : ℝ) / (d : ℝ) ^ j)) ≤ B)
    (k : ℕ) (S : Finset V) (u : V) (hu : u ∈ S) :
    WeightedTree.truncatedTotal (computationTree G lam k S u) k ≤
      1 + (d + 1 : ℕ) * pmax lam * B := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hp0 := pmax_nonneg (le_of_lt hlam)
  let t := computationTree G lam k S u
  have hl : WeightedTree.ProperlyLabeled G S t := computationTree_properlyLabeled G lam k S u hu
  have hg : ∀ c ∈ t.children, WeightedTree.Good (d : ℝ) (pmax lam) c :=
    computationTree_good_children G hlam d hd hcritical hdegree k S u
  have hlen : t.children.length ≤ d + 1 := by
    cases k with
    | zero => simp [t]
    | succ k =>
        rw [show t = computationTree G lam (k+1) S u from rfl, computationTree_children_length]
        exact (neighborList_length_le_degree G S u).trans (hdegree u)
  have hc : ∀ c ∈ t.children,
      (∑ j ∈ Finset.range k, c.mass j) ≤ pmax lam * B := by
    intro c hc
    have ha : G.Adj u c.label := by simpa [t] using hl.adjacent hc
    have hs : WeightedTree.ProperlyLabeled G (S.erase u) c := by
      simpa [t] using hl.child hc
    calc
      (∑ j ∈ Finset.range k, c.mass j) ≤
          ∑ j ∈ Finset.range k, pmax lam *
            Real.sqrt ((orientedCount H (e u) (e c.label) j : ℝ) / (d : ℝ) ^ j) := by
        apply Finset.sum_le_sum
        intro j _
        exact WeightedTree.mass_le_sqrt_orientedCount e hd0 hp0 (hg c hc) hs
          (Finset.not_mem_erase _ _) ha j
      _ = pmax lam * (∑ j ∈ Finset.range k,
          Real.sqrt ((orientedCount H (e u) (e c.label) j : ℝ) / (d : ℝ) ^ j)) := by
        rw [Finset.mul_sum]
      _ ≤ pmax lam * B :=
        mul_le_mul_of_nonneg_left (hwalks _ _ (e.map_adj_iff.mpr ha) k) hp0
  change t.truncatedTotal k ≤ _
  unfold WeightedTree.truncatedTotal WeightedTree.forestMass
  rw [sum_range_map_swap]
  calc
    1 + (t.children.map (fun c => ∑ j ∈ Finset.range k, c.mass j)).sum ≤
        1 + (t.children.map (fun _ => pmax lam * B)).sum :=
      add_le_add_left (List.sum_le_sum hc) 1
    _ = 1 + (t.children.length : ℝ) * (pmax lam * B) := by simp
    _ ≤ 1 + (d + 1 : ℕ) * pmax lam * B := by
      have hc' : (t.children.length : ℝ) ≤ ((d+1 : ℕ) : ℝ) := by exact_mod_cast hlen
      have hmul := mul_le_mul_of_nonneg_right hc' (mul_nonneg hp0 hB)
      nlinarith

/-- The actual diagonal-one influence row, not an abstract tree surrogate. -/
theorem influence_bound_from_walks
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) (e : G ↪g H)
    {lam B : ℝ} (hlam : 0 < lam) (hB : 0 ≤ B)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    (hdegree : ∀ v : V, G.degree v ≤ d + 1)
    (hwalks : ∀ a b : W, H.Adj a b → ∀ K : ℕ,
      (∑ j ∈ Finset.range K,
        Real.sqrt ((orientedCount H a b j : ℝ) / (d : ℝ) ^ j)) ≤ B)
    (S : Finset V) (u : V) (hu : u ∈ S) :
    (∑ v ∈ S, |coordinateInfluence G lam S u v|) ≤ 1 + (d+1 : ℕ) * pmax lam * B := by
  apply influence_row_sum_le G hlam hu
  intro f hf
  exact (observableInfluence_le_computationTree G hlam S.card S u hu (le_refl _) f
    (fun v _ => hf v)).trans
    (computationTree_bound_from_walks G H e hlam hB d hd hcritical hdegree hwalks
      S.card S u hu)

end CriticalHardcore
