import LambertScale

noncomputable section
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

def logError (n : ℕ) (lam v : ℂ) : ℂ :=
  (n : ℂ) * (Complex.log (Q (reciprocalCoordinate lam v)) -
    Complex.log (P (reciprocalCoordinate lam v)) + 2 * reciprocalCoordinate lam v ^ 2)

def perturbation (n : ℕ) (lam v : ℂ) : ℂ := v ^ 2 / (2 * lam) + logError n lam v

def A (n : ℕ) (lam v : ℂ) : ℂ :=
  reciprocalCoordinate lam v * Complex.exp ((n : ℂ) *
    (Complex.log (Q (reciprocalCoordinate lam v)) - Complex.log (P (reciprocalCoordinate lam v))))

def B (n : ℕ) (lam v : ℂ) : ℂ :=
  reciprocalCoordinate lam v ^ (2 * n + 1) *
    Complex.exp (-((n : ℂ) * Complex.log (P (reciprocalCoordinate lam v))))

def H (n : ℕ) (lam v : ℂ) : ℂ := 1 + A n lam v - B n lam v

theorem lam_ne_zero {n : ℕ} (hn : 0 < n) {lam : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ))) : lam ≠ 0 := by
  have hn0 : 4 * (n : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hn.ne')
  intro h
  apply neg_ne_zero.mpr hn0
  simpa only [h, zero_mul] using he.symm

theorem exponent_identity {n : ℕ} (hn : 0 < n) {lam : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ))) (v : ℂ) :
    -2 * (n : ℂ) * reciprocalCoordinate lam v ^ 2 =
      lam / 2 + v + v ^ 2 / (2 * lam) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlam0 := lam_ne_zero hn he
  dsimp [reciprocalCoordinate]
  rw [mul_pow, initialCoordinate_square hn he]
  field_simp [hn0, hlam0]
  ring

theorem A_exact {n : ℕ} (hn : 0 < n) {lam : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ))) (v : ℂ) :
    A n lam v = -(1 + v / lam) * Complex.exp (v + perturbation n lam v) := by
  have hx : (n : ℂ) * (Complex.log (Q (reciprocalCoordinate lam v)) -
      Complex.log (P (reciprocalCoordinate lam v))) =
      lam / 2 + (v + perturbation n lam v) := by
    dsimp [perturbation, logError]
    linear_combination exponent_identity hn he v
  rw [A, hx, Complex.exp_add]
  calc
    reciprocalCoordinate lam v * (Complex.exp (lam / 2) * Complex.exp (v + perturbation n lam v)) =
        (initialCoordinate lam * Complex.exp (lam / 2)) *
          ((1 + v / lam) * Complex.exp (v + perturbation n lam v)) := by
      dsimp [reciprocalCoordinate]
      ring
    _ = _ := by rw [initialCoordinate_half_exp]; ring

theorem A_eq_rational {n : ℕ} {lam v : ℂ}
    (hp : P (reciprocalCoordinate lam v) ≠ 0)
    (hq : Q (reciprocalCoordinate lam v) ≠ 0) :
    A n lam v = reciprocalCoordinate lam v *
      (Q (reciprocalCoordinate lam v) / P (reciprocalCoordinate lam v)) ^ n := by
  simp only [A, Complex.exp_nat_mul, Complex.exp_sub, Complex.exp_log hp, Complex.exp_log hq]

theorem B_eq_rational {n : ℕ} {lam v : ℂ}
    (hp : P (reciprocalCoordinate lam v) ≠ 0) :
    B n lam v = reciprocalCoordinate lam v ^ (2 * n + 1) /
      P (reciprocalCoordinate lam v) ^ n := by
  simp only [B, Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_log hp, div_eq_mul_inv]

#print axioms exponent_identity
#print axioms A_exact
#print axioms A_eq_rational
#print axioms B_eq_rational
end Transfer
end SquareFlowerCompletion
