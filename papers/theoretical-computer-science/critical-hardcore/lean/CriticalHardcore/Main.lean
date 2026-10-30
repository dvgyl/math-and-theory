import CriticalHardcore.CollisionBound
import CriticalHardcore.InfluenceTransfer
import CriticalHardcore.RegularCompletion
import CriticalHardcore.ScaleInterpretation
import CriticalHardcore.SpectralStatement

/-!
# Critical hard-core influence bound

The final theorems concern the actual finite independent-set distribution,
including all feasible pinnings. No tree comparison, collision theorem,
independence property, or spectral-independence assumption is left as a premise.

Here `d + 1` is the maximum-degree bound, and `criticalActivity d` is exactly
`d ^ d / (d - 1) ^ (d + 1)`, the usual hard-core tree-uniqueness threshold.
-/

open scoped BigOperators

namespace CriticalHardcore

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def criticalInfluenceBound (d n : ℕ) (lam : ℝ) : ℝ :=
  1 + (d + 1 : ℕ) * pmax lam * collisionScale d (2 * (d + 1) * n)

/-- The central absolute-row-sum theorem, for every induced free-vertex set. -/
theorem critical_hardcore_influence_rows
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    (hdegree : ∀ v : V, G.degree v ≤ d + 1)
    (S : Finset V) (u : V) (hu : u ∈ S) :
    (∑ v ∈ S, |coordinateInfluence G lam S u v|) ≤
      criticalInfluenceBound d (Fintype.card V) lam := by
  letI : NeZero (d + 1) := ⟨by omega⟩
  let H := RegularCompletion.graph G (d + 1)
  let e := RegularCompletion.canonicalEmbedding G (d + 1)
  have hregular : H.IsRegularOfDegree (d + 1) :=
    RegularCompletion.regular G (d + 1) hdegree
  have hsize : Fintype.card (RegularCompletion.Vertex V (d + 1)) =
      2 * (d + 1) * Fintype.card V := RegularCompletion.card_vertex (d + 1)
  have hb := influence_bound_from_walks G H e hlam
    (Nat.cast_nonneg (collisionScale d (Fintype.card (RegularCompletion.Vertex V (d + 1)))))
    d hd hcritical hdegree
    (regular_survival_sqrt_sum_le_scale H d hd hregular) S u hu
  simpa only [hsize, criticalInfluenceBound] using hb

/-- Critical l-infinity spectral independence under every feasible pinning,
with the diagonal-one convention and actual nondegenerate Gibbs marginals. -/
theorem critical_hardcore_spectral_independence
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    (hdegree : ∀ v : V, G.degree v ≤ d + 1) :
    LinftySpectrallyIndependent G lam
      (criticalInfluenceBound d (Fintype.card V) lam) := by
  apply linftySpectralIndependence_of_residual_rows G hlam
  exact critical_hardcore_influence_rows G hlam d hd hcritical hdegree

/-- The same explicit theorem with all pinning sets and normalizers visible. -/
theorem critical_hardcore_pinned_rows
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    (hdegree : ∀ v : V, G.degree v ≤ d + 1)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : 0 < pinnedOccupation G lam S P Q u ∧
      pinnedOccupation G lam S P Q u < 1) :
    (∑ v ∈ S, |pinnedCoordinateInfluence G lam S P Q u v|) ≤
      criticalInfluenceBound d (Fintype.card V) lam := by
  exact all_pinned_rows_of_residual_rows G hlam
    (critical_hardcore_influence_rows G hlam d hd hcritical hdegree) hp hu

/-- A conventional real square-root/logarithm upper bound on the explicit
constant. For fixed degree this is `O(sqrt(n) * log(n+1))`. -/
theorem criticalInfluenceBound_le_real
    {lam : ℝ} (hlam : 0 ≤ lam) (d n : ℕ) (hd : 2 ≤ d) :
    criticalInfluenceBound d n lam ≤
      1 + (d + 1 : ℕ) * pmax lam *
        (12 * (d : ℝ) * (Real.sqrt ((2 * (d + 1) * n : ℕ) : ℝ) + 1) *
          (1 + Real.logb (d : ℝ) (Real.sqrt ((2 * (d + 1) * n : ℕ) : ℝ) + 1))) := by
  unfold criticalInfluenceBound
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left (collisionScale_le_real hd)
    (mul_nonneg (Nat.cast_nonneg _) (pmax_nonneg hlam))

end CriticalHardcore
