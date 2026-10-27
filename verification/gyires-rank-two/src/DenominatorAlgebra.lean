module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MathAndTheory.Gyires.RankTwo.Certificate

lemma pow_square_swap (z : ℝ) (k : ℕ) : (z^2)^k = (z^k)^2 := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem cancel_common_power (q g z : ℝ) (n k : ℕ) (hk : k ≤ n)
    (hq : q ≠ 0) (hg : g ≠ 0) :
    z*q^(n-k)/(g*q^n) = z/(g*q^k) := by
  have hp : q^n = q^(n-k)*q^k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hp]
  field_simp [hq, hg]

theorem cleared_cross_term (N m l s D f g e h : ℝ) (n k : ℕ)
    (hk : k ≤ n) (hN : N ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0)
    (hs : s ≠ 0) (hD : D ≠ 0) (hg : g ≠ 0) :
    (f/(g*(D/(N^2*s^2))^k))*e*h =
      f*(N*m*s)^k*e*(N*l*s)^k*h*(m*l)^(n-k)*D^(n-k)/
        (g*m^n*l^n*D^n) := by
  have hq : m*l*D ≠ 0 := mul_ne_zero (mul_ne_zero hm hl) hD
  have hcanon :
      f*(N*m*s)^k*e*(N*l*s)^k*h*(m*l)^(n-k)*D^(n-k)/
        (g*m^n*l^n*D^n) =
      (f*(N*m*s)^k*e*(N*l*s)^k*h)*(m*l*D)^(n-k)/(g*(m*l*D)^n) := by
    simp only [mul_pow]
    ring
  rw [hcanon, cancel_common_power _ _ _ n k hk hq hg]
  simp only [mul_pow, div_pow, pow_square_swap]
  field_simp [hN, hm, hl, hs, hD, hg]

theorem cleared_gram_term (N m l s D K f g e : ℝ) (n k : ℕ)
    (hk : k ≤ n) (hN : N ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0)
    (hs : s ≠ 0) (hD : D ≠ 0) (hg : g ≠ 0) :
    (f/(g*(D/(N^2*s^2))^k))*e^2*(K/(l*D))^k =
      f*((N*m*s)^k*e)^2*K^k*m^(2*(n-k))*l^(n-k)*D^(2*(n-k))/
        (g*m^(2*n)*l^n*D^(2*n)) := by
  have hq : m^2*l*D^2 ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hm) hl)
    (pow_ne_zero 2 hD)
  have hcanon :
      f*((N*m*s)^k*e)^2*K^k*m^(2*(n-k))*l^(n-k)*D^(2*(n-k))/
        (g*m^(2*n)*l^n*D^(2*n)) =
      (f*((N*m*s)^k*e)^2*K^k)*(m^2*l*D^2)^(n-k)/(g*(m^2*l*D^2)^n) := by
    simp only [mul_pow, pow_mul]
    ring
  rw [hcanon, cancel_common_power _ _ _ n k hk hq hg]
  simp only [mul_pow, div_pow, pow_square_swap]
  field_simp [hN, hm, hl, hs, hD, hg]

theorem contraction_fraction (m l D C G g : ℝ) (n : ℕ)
    (hm : m ≠ 0) (hl : l ≠ 0) (hD : D ≠ 0) (hg : g ≠ 0) :
    C/(g*m^n*l^n*D^n)-G/(g*m^(2*n)*l^n*D^(2*n)) =
      (m^n*C*D^n-G)/(g*m^(2*n)*l^n*D^(2*n)) := by
  rw [show 2*n = n+n by omega]
  simp only [pow_add]
  field_simp [hm, hl, hD, hg]

end MathAndTheory.Gyires.RankTwo.Certificate
