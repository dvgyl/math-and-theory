import CriticalHardcore.Pinning

/-!
The semantic statement of l-infinity spectral independence. It quantifies
over all feasible pinning events in the actual independent-set distribution
and over precisely the coordinates whose pinned marginals are nondegenerate.
The diagonal-one convention agrees with Chen--Jiang (2026), Definition 2.1.
-/

open scoped BigOperators

namespace CriticalHardcore

variable {V : Type*} [Fintype V] [DecidableEq V]

def LinftySpectrallyIndependent (G : SimpleGraph V) (lam C : ℝ) : Prop :=
  ∀ P Q : Finset V, FeasiblePinning G Finset.univ P Q → ∀ u : V,
    (0 < pinnedOccupation G lam Finset.univ P Q u ∧
      pinnedOccupation G lam Finset.univ P Q u < 1) →
    (∑ v : V, |pinnedCoordinateInfluence G lam Finset.univ P Q u v|) ≤ C

theorem linftySpectralIndependence_of_residual_rows (G : SimpleGraph V)
    {lam C : ℝ} (hlam : 0 < lam)
    (hrows : ∀ S : Finset V, ∀ u ∈ S,
      (∑ v ∈ S, |coordinateInfluence G lam S u v|) ≤ C) :
    LinftySpectrallyIndependent G lam C := by
  intro P Q hp u hu
  have huf := (pinnedOccupation_nondegenerate_iff G hlam hp u).mp hu
  have hsum := pinned_influence_row_sum_eq G hlam hp huf
  simpa only [hsum] using hrows (pinningFree G Finset.univ P Q) u huf

theorem all_pinned_rows_of_residual_rows (G : SimpleGraph V)
    {lam C : ℝ} (hlam : 0 < lam)
    (hrows : ∀ S : Finset V, ∀ u ∈ S,
      (∑ v ∈ S, |coordinateInfluence G lam S u v|) ≤ C)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : 0 < pinnedOccupation G lam S P Q u ∧ pinnedOccupation G lam S P Q u < 1) :
    (∑ v ∈ S, |pinnedCoordinateInfluence G lam S P Q u v|) ≤ C := by
  have huf := (pinnedOccupation_nondegenerate_iff G hlam hp u).mp hu
  rw [pinned_influence_row_sum_eq G hlam hp huf]
  exact hrows _ _ huf

end CriticalHardcore
