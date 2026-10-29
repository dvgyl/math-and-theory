import Certificates

set_option maxHeartbeats 2000000
noncomputable section
namespace Motzkin.Forcing
open Motzkin.Certificate

theorem corner_gap (n : ℝ) (hn : 12 ≤ n) :
    800/(n+3)^3 < F n (U n) (-E n) (E n) := by
  have h3 : 0 < n+3 := by linarith
  have h4 : 0 < n+4 := by linarith
  have h5 : 0 < n+5 := by linarith
  have hred : 0 < reducedDenominator n := by unfold reducedDenominator; positivity
  have hpoly := quantitative_polynomial_pos n hn
  have hscaled := corner_scaled n (ne_of_gt h3) (ne_of_gt h4) (ne_of_gt h5)
  have hid : fullDenominator n = (n+3)^3*reducedDenominator n := by
    dsimp [fullDenominator,reducedDenominator]; ring
  apply (div_lt_iff₀ (pow_pos h3 3)).2
  apply (mul_lt_mul_right hred).mp
  calc
    800*reducedDenominator n < P n := hpoly
    _ = (F n (U n) (-E n) (E n)*(n+3)^3)*reducedDenominator n := by
      rw [←hscaled,hid]
      ring

#print axioms corner_gap
end Motzkin.Forcing
