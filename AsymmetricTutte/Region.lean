module
public import AsymmetricTutte.PublicDefs
import all AsymmetricTutte.Parameters
import all AsymmetricTutte.Sufficiency


section

namespace AsymmetricTutte

open Results.TutteThreshold


theorem region_sufficiency {α : Type*} (M : Matroid α) [M.Finite]
    (hM : IsAdmissible M) {x y : ℝ} (hR : Region x y) :
    tutte M 1 1 ^ 2 ≤ tutte M x 0 * tutte M 0 y :=
  matroid_sufficiency M hM hR.scalarInputs hR.swap.scalarInputs

end AsymmetricTutte
