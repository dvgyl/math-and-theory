module
public import AsymmetricTutte.PublicDefs
import all TutteSource.TutteThreshold.Solution.Bridge
import all TutteSource.TutteThreshold.Solution.Posit

section

open Matroid Results.TutteThreshold

namespace AsymmetricTutte

lemma public_toRk_r {α : Type*} (M : Matroid α) [M.Finite] [DecidableEq α]
    (S : Finset α) : (toRk M).r S = rk M (S : Set α) := by
  exact toRk_r M S

lemma public_tutte_eq_Z {α : Type*} (M : Matroid α) [M.Finite] [DecidableEq α]
    (x y : ℝ) :
    tutte M x y = (toRk M).Z (x - 1) (y - 1) (fun _ => ((1 : ℝ), (1 : ℝ))) := by
  exact tutte_eq_Z M x y

end AsymmetricTutte
