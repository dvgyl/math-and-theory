module
public import AsymmetricTutte.PublicDefs
import all AsymmetricTutte.Region
import all AsymmetricTutte.Necessity.Endpoints


@[expose] public section

/-!
The exact nonnegative parameter region for the universal asymmetric
Tutte-polynomial product inequality. All numerical side conditions in
the matroid induction are discharged here.
-/

namespace AsymmetricTutte

open Results.TutteThreshold

theorem universal_iff_region {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    AsymmetricMerinoWelsh.Universal x y ↔ Region x y := by
  constructor
  · intro hU
    obtain ⟨hx1, hy1, hc⟩ := AsymmetricMerinoWelsh.necessary_conditions hx hy hU
    exact ⟨hx1, hy1, fun k hk => (hc k hk).1, fun k hk => (hc k hk).2⟩
  · intro hR α M inst hM
    exact region_sufficiency M hM hR

end AsymmetricTutte
