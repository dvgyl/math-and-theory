module
public import AsymmetricTutte.PublicDefs
import all AsymmetricTutte.Inputs
import all AsymmetricTutte.Scalar
import all AsymmetricTutte.XY


section

namespace AsymmetricTutte

theorem Region.swap {x y : ℝ} (hR : Region x y) : Region y x :=
  ⟨hR.2.1, hR.1, hR.2.2.2, hR.2.2.1⟩

theorem Region.shifted_product_gt_one {x y : ℝ} (hR : Region x y) :
    1 < (x - 1) * (y - 1) :=
  curves_force_shifted_product_gt_one x y hR.1 hR.2.1 hR.2.2.1 hR.2.2.2

theorem Region.scalarInputs {x y : ℝ} (hR : Region x y) : ScalarInputs x y := by
  have hXY := hR.shifted_product_gt_one
  refine ⟨hR.1, hR.2.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact region_rank_one x y hR hXY k hk
  · intro A B U V s t hA hB hU hV hs ht hAU hBV
    exact cauchy_step A B U V s t hA hB hU hV hs ht hAU hBV
  · intro k hk A B U V s t hA hB hU hV hs ht hAB hVU hAU hBV
    exact region_scalar x y hR hXY k hk A B U V s t hA hB hU hV hAB hVU hs ht hAU hBV
  · intro k hk A B V s t hA hB hV hs ht hAB hBV hst
    exact region_coloop_step x y hR hXY k hk A B V s t hA hB hV hAB hs ht hst hBV


end AsymmetricTutte
