import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option maxHeartbeats 2000000

namespace Motzkin.Algebra

theorem ratio_difference (r s y z a b : ℝ) :
    (y+a*(s-r))^3-s^3*(z+b*(s-r))-(y^3-r^3*z) =
    (s-r)*(a*((y+a*(s-r))^2+(y+a*(s-r))*y+y^2)-
      (s^2+s*r+r^2)*z-s^3*b) := by ring

theorem first_error_difference (r y z g d t : ℝ) :
    (y+g*t)^3-r^3*(z+d*t)-(y^3-r^3*z) =
      t*(g*((y+g*t)^2+(y+g*t)*y+y^2)-r^3*d) := by ring

theorem second_error_difference (r y z d t : ℝ) :
    y^3-r^3*(z+d*t)-(y^3-r^3*z) = -r^3*d*t := by ring

theorem y_upper_deficit (a b : ℝ) :
    243-(a^2+a*b+b^2) =
      (9-a)*(9+a)+(9-b)*(9+b)+(9-a)*b+9*(9-b) := by ring

theorem y_lower_surplus (a b : ℝ) :
    (a^2+a*b+b^2)-147 =
      (a-7)*(a+7)+(b-7)*(b+7)+(a-7)*b+7*(b-7) := by ring

theorem r_lower_surplus (r s : ℝ) :
    r^2+r*s+s^2-3*(8/3:ℝ)^2 =
      (r-8/3)*(r+8/3)+(s-8/3)*(s+8/3)+
        (s-8/3)*r+(8/3)*(r-8/3) := by ring

theorem r_factor_margin (r s y₁ y₂ a z b : ℝ) :
    -(a*(y₁^2+y₁*y₂+y₂^2)-z*(r^2+r*s+s^2)-b*s^3)-(382/27:ℝ) =
    (2-a)*(y₁^2+y₁*y₂+y₂^2)+2*(243-(y₁^2+y₁*y₂+y₂^2))+
    (z-19)*(r^2+r*s+s^2)+19*(r^2+r*s+s^2-3*(8/3:ℝ)^2)+
    (b-5)*s^3+5*(s^3-(8/3:ℝ)^3) := by ring

theorem error_factor_margin (r y₁ y₂ e : ℝ) :
    y₁^2+y₁*y₂+y₂^2-e*r^3-93 =
      (y₁^2+y₁*y₂+y₂^2-147)+(2-e)*r^3+2*(27-r^3) := by ring

/-- Universal exponent identities underlying the multiplicative root transfer. -/
theorem transfer_exponents (n : ℤ) :
    (-(n*(n+1)) + n*(n+1) = 0) ∧
    (2*(n^2-1)-3*n*(n+1) = -(n+1)*(n+2)) ∧
    (-n*(n-1)+3*n*(n+1) = 2*((n+1)^2-1)) ∧
    (0-n*(n+1) = -n*(n+1)) := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- A fully quantified abstract propagation lemma for the additive defect.
It does not assert that a particular Motzkin sequence satisfies its hypotheses. -/
def defect (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  2*(((k:ℝ)+1)^2-1)*b (k+1)-
  ((k:ℝ)+1)*((k:ℝ)+2)*b k-((k:ℝ)+1)*(k:ℝ)*b (k+2)

theorem defect_step (b : ℕ → ℝ) (k : ℕ) :
    defect b (k+1)-defect b k =
      ((k:ℝ)+1)*((k:ℝ)+2)*(b k-3*b (k+1)+3*b (k+2)-b (k+3)) := by
  simp only [defect, Nat.cast_add, Nat.cast_one, Nat.add_assoc]
  norm_num
  ring

theorem propagate_defect (b : ℕ → ℝ)
    (hbase : 0 < defect b 10)
    (hthird : ∀ k : ℕ, 10 ≤ k → 0 < b k-3*b (k+1)+3*b (k+2)-b (k+3)) :
    ∀ k : ℕ, 10 ≤ k → 0 < defect b k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
      have hf : 0 < ((k:ℝ)+1)*((k:ℝ)+2) := by positivity
      have hp := mul_pos hf (hthird k hk)
      have he := defect_step b k
      linarith

end Motzkin.Algebra
