import ReciprocalModel
import ReciprocalPrefactor

noncomputable section
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

def logDerivative (w : ℂ) : ℂ := -(4 * w + 6 * w ^ 2) / (P w * Q w)

theorem logDerivative_eq_K (w : ℂ) : logDerivative w = -4 * w * K w := by
  dsimp [logDerivative, K]
  ring

theorem factor_identity (N a lam v : ℂ) (hroot : -4 * N * a ^ 2 = lam)
    (hlam : lam ≠ 0) (hv : lam + v ≠ 0)
    (_hp : P (a * (1 + v / lam)) ≠ 0) (_hq : Q (a * (1 + v / lam)) ≠ 0) :
    a / lam + (a * (1 + v / lam)) * N * logDerivative (a * (1 + v / lam)) * (a / lam) =
      (a * (1 + v / lam)) * derivativeFactor lam (a * (1 + v / lam)) v := by
  have ha : a / lam = (a * (1 + v / lam)) * (lam + v)⁻¹ := by
    field_simp [hlam, hv]
    ring
  have hb : -4 * N * (a * (1 + v / lam)) * (a / lam) = 1 + v / lam := by
    calc
      _ = (-4 * N * a ^ 2) / lam * (1 + v / lam) := by ring
      _ = lam / lam * (1 + v / lam) := by rw [hroot]
      _ = _ := by rw [div_self hlam, one_mul]
  rw [logDerivative_eq_K]
  calc
    _ = a / lam + (a * (1 + v / lam)) * K (a * (1 + v / lam)) *
        (-4 * N * (a * (1 + v / lam)) * (a / lam)) := by ring
    _ = a / lam + (a * (1 + v / lam)) * K (a * (1 + v / lam)) * (1 + v / lam) := by rw [hb]
    _ = _ := by rw [ha]; dsimp [derivativeFactor]; ring

theorem hasDerivAt_coordinate (lam v : ℂ) :
    HasDerivAt (reciprocalCoordinate lam) (initialCoordinate lam / lam) v := by
  convert (((hasDerivAt_const v (1 : ℂ)).add ((hasDerivAt_id v).div_const lam)).const_mul
    (initialCoordinate lam)) using 1
  dsimp [reciprocalCoordinate]
  ring

theorem logDerivative_eq (w : ℂ) (hp : P w ≠ 0) (hq : Q w ≠ 0) :
    logDerivative w = (Q w)⁻¹ * (3 + 2 * w) - (P w)⁻¹ * (3 + 6 * w) := by
  dsimp [logDerivative]
  field_simp [hp, hq]
  dsimp [P, Q]
  ring

theorem hasDerivAt_log_ratio {lam v : ℂ}
    (hw : ‖reciprocalCoordinate lam v‖ ≤ (1 / 16 : ℝ)) :
    HasDerivAt
      (fun z => Complex.log (Q (reciprocalCoordinate lam z)) -
        Complex.log (P (reciprocalCoordinate lam z)))
      (logDerivative (reciprocalCoordinate lam v) * (initialCoordinate lam / lam)) v := by
  let w := reciprocalCoordinate lam v
  obtain ⟨hp, hq⟩ := slitPlane_bounds hw
  have hp0 := Complex.slitPlane_ne_zero hp
  have hq0 := Complex.slitPlane_ne_zero hq
  have hP : HasDerivAt P (3 + 6 * w) w := by
    convert (((hasDerivAt_const w (1 : ℂ)).add ((hasDerivAt_id w).const_mul 3)).add
      (((hasDerivAt_id w).pow 2).const_mul 3)) using 1; dsimp [P]; ring
  have hQ : HasDerivAt Q (3 + 2 * w) w := by
    convert (((hasDerivAt_const w (1 : ℂ)).add ((hasDerivAt_id w).const_mul 3)).add
      ((hasDerivAt_id w).pow 2)) using 1; dsimp [Q]; ring
  have hc := hasDerivAt_coordinate lam v
  have h := ((Complex.hasDerivAt_log hq).comp v (hQ.comp v hc)).sub
    ((Complex.hasDerivAt_log hp).comp v (hP.comp v hc))
  convert h using 1
  rw [logDerivative_eq _ hp0 hq0]
  ring

/-- The exact derivative of the actual exponential reciprocal term. -/
theorem hasDerivAt_A {n : ℕ} (hn : 0 < n) {lam v : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ)))
    (hv : lam + v ≠ 0) (hw : ‖reciprocalCoordinate lam v‖ ≤ (1 / 16 : ℝ)) :
    HasDerivAt (A n lam)
      (A n lam v * derivativeFactor lam (reciprocalCoordinate lam v) v) v := by
  let w := reciprocalCoordinate lam v
  let a := initialCoordinate lam
  let E := Complex.exp ((n : ℂ) * (Complex.log (Q w) - Complex.log (P w)))
  have hroot : -4 * (n : ℂ) * a ^ 2 = lam := by
    have h := exponent_identity hn he 0
    simp only [reciprocalCoordinate, zero_div, add_zero, mul_one, zero_pow (by decide : 2 ≠ 0), zero_add, zero_mul] at h
    dsimp [a]
    linear_combination 2 * h
  obtain ⟨hp, hq⟩ := slitPlane_bounds hw
  have hfactor := factor_identity (n : ℂ) a lam v hroot (lam_ne_zero hn he) hv
    (Complex.slitPlane_ne_zero hp) (Complex.slitPlane_ne_zero hq)
  change a / lam + w * (n : ℂ) * logDerivative w * (a / lam) =
    w * derivativeFactor lam w v at hfactor
  have hc := hasDerivAt_coordinate lam v
  have hl := hasDerivAt_log_ratio hw
  have hx := (Complex.hasDerivAt_exp _).comp v (hl.const_mul (n : ℂ))
  have hA := hc.mul hx
  convert hA using 1
  change (w * E) * derivativeFactor lam w v =
    (a / lam) * E + w * (E * ((n : ℂ) * (logDerivative w * (a / lam))))
  linear_combination -E * hfactor

#print axioms factor_identity
#print axioms hasDerivAt_log_ratio
#print axioms hasDerivAt_A
end Transfer
end SquareFlowerCompletion
