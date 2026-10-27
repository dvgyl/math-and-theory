module

public import RootBound

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix Equiv PermutationTransfer PermutationCycle PermutationMatrixBridge

noncomputable def powerSum (B C : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => B
  | n+2 => B * powerSum B C (n+1) - C * powerSum B C n

theorem root_power_recurrence (r s : ℝ) (n : ℕ) :
    r^(n+2)+s^(n+2) = (r+s)*(r^(n+1)+s^(n+1)) - r*s*(r^n+s^n) := by
  simp only [pow_add, pow_one, pow_two]
  ring

theorem powerSum_eq_roots (r s : ℝ) (n : ℕ) :
    powerSum (r+s) (r*s) n = r^n+s^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [powerSum]
  | one => simp [powerSum]
  | more n h0 h1 =>
    rw [powerSum, h0, h1]
    exact (root_power_recurrence r s n).symm

theorem roots_product {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    positiveRoot a b c * negativeRoot a b c = -(a*c) := by
  have h := (positiveRoot_properties ha hb hc).2.2
  dsimp [negativeRoot]
  nlinarith

noncomputable def permanentSquareExpr (n : ℕ) (a b c : ℝ) : ℝ :=
  a^(2*n) + c^(2*n) + powerSum (b^2+2*a*c) ((a*c)^2) n +
    2*powerSum (a*b) (-(a^3*c)) n + 2*powerSum (c*b) (-(a*c^3)) n +
    2*(a*c)^n + 2*(-(a*c))^n

theorem power_twice (r : ℝ) (n : ℕ) : (r^2)^n = (r^n)^2 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]

theorem permanentSquareExpr_eq_roots {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    permanentSquareExpr n a b c =
      (a^n+c^n+positiveRoot a b c ^ n+negativeRoot a b c ^ n)^2 := by
  let r := positiveRoot a b c
  let s := negativeRoot a b c
  have hsum : r+s=b := roots_sum a b c
  have hprod : r*s=-(a*c) := roots_product ha hb hc
  have hsqsum : r^2+s^2=b^2+2*a*c := by
    calc
      r^2+s^2 = (r+s)^2-2*(r*s) := by ring
      _ = b^2+2*a*c := by rw [hsum, hprod]; ring
  have hsqprod : r^2*s^2=(a*c)^2 := by
    calc
      r^2*s^2 = (r*s)^2 := by ring
      _ = (a*c)^2 := by rw [hprod]; ring
  have har : a*r+a*s=a*b := by rw [← mul_add, hsum]
  have hap : (a*r)*(a*s)=-(a^3*c) := by
    calc
      (a*r)*(a*s) = a^2*(r*s) := by ring
      _ = -(a^3*c) := by rw [hprod]; ring
  have hcr : c*r+c*s=c*b := by rw [← mul_add, hsum]
  have hcp : (c*r)*(c*s)=-(a*c^3) := by
    calc
      (c*r)*(c*s) = c^2*(r*s) := by ring
      _ = -(a*c^3) := by rw [hprod]; ring
  have hu := powerSum_eq_roots (r^2) (s^2) n
  rw [hsqsum, hsqprod, power_twice, power_twice] at hu
  have hv := powerSum_eq_roots (a*r) (a*s) n
  rw [har, hap] at hv
  have hw := powerSum_eq_roots (c*r) (c*s) n
  rw [hcr, hcp] at hw
  change permanentSquareExpr n a b c = (a^n+c^n+r^n+s^n)^2
  unfold permanentSquareExpr
  rw [hu, hv, hw, ← hprod]
  simp only [mul_pow]
  rw [pow_mul, pow_mul, power_twice, power_twice]
  ring

theorem actual_permanent_square (n : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (polynomialMatrix (finRotate (n+1)) a b c).permanent^2 =
      permanentSquareExpr (n+1) a b c := by
  rw [cycle_permanent_eq_roots n ha hb hc, permanentSquareExpr_eq_roots ha hb hc]

end MathAndTheory.Gyires.PermutationFinite
