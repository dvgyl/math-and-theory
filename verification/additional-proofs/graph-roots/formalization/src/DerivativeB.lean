import DerivativeA

noncomputable section
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

def BD (n : ℕ) (lam v : ℂ) : ℂ :=
  (initialCoordinate lam / lam) * reciprocalCoordinate lam v ^ (2 * n) *
    Complex.exp (-((n : ℂ) * Complex.log (P (reciprocalCoordinate lam v)))) *
      ((2 * (n : ℂ) + 1) - (n : ℂ) * reciprocalCoordinate lam v *
        (3 + 6 * reciprocalCoordinate lam v) / P (reciprocalCoordinate lam v))

/-- The exact derivative keeps the differentiated exponentially small term. -/
theorem hasDerivAt_B {n : ℕ} {lam v : ℂ}
    (hw : ‖reciprocalCoordinate lam v‖ ≤ (1 / 16 : ℝ)) :
    HasDerivAt (B n lam) (BD n lam v) v := by
  let w := reciprocalCoordinate lam v
  obtain ⟨hp, hq⟩ := slitPlane_bounds hw
  have hp0 := Complex.slitPlane_ne_zero hp
  have hP : HasDerivAt P (3 + 6 * w) w := by
    convert (((hasDerivAt_const w (1 : ℂ)).add ((hasDerivAt_id w).const_mul 3)).add
      (((hasDerivAt_id w).pow 2).const_mul 3)) using 1; dsimp [P]; ring
  have hc := hasDerivAt_coordinate lam v
  have hlog := (Complex.hasDerivAt_log hp).comp v (hP.comp v hc)
  have hExp := (Complex.hasDerivAt_exp _).comp v ((hlog.const_mul (n : ℂ)).neg)
  have hPow := hc.pow (2 * n + 1)
  have hB := hPow.mul hExp
  convert hB using 1
  dsimp [BD]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv]
  rw [pow_succ]
  ring

#print axioms hasDerivAt_B
end Transfer
end SquareFlowerCompletion
