module
public import AsymmetricTutte.Scalar


@[expose] public section

/-!
An exact nonredundancy certificate: the two k=2 boundary conditions, even
combined with (x-1)(y-1)>1, do not imply all of the boundary conditions.
-/

namespace AsymmetricTutte

private lemma example_small_root :
    Real.sqrt ((101 / 100 : ℝ) - 1) = 1 / 10 := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
  norm_num

private lemma example_large_root_square : (Real.sqrt (300 : ℝ))^2 = 300 :=
  Real.sq_sqrt (by norm_num)

private lemma example_large_root_upper : Real.sqrt (300 : ℝ) < 35 / 2 := by
  apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
  norm_num

private lemma example_large_root_lower : (433 / 25 : ℝ) < Real.sqrt 300 := by
  apply (Real.lt_sqrt (by norm_num)).2
  norm_num

lemma example_parameters_gt_one : (1 : ℝ) < 301 ∧ (1 : ℝ) < 101 / 100 := by
  norm_num

lemma example_shifted_product_gt_one :
    (1 : ℝ) < (301 - 1) * (101 / 100 - 1) := by
  norm_num

lemma example_forward_two :
    (Real.sqrt ((301 : ℝ) - 1) + 2 * Real.sqrt ((101 / 100 : ℝ) - 1))^2 ≤
      (301 : ℝ) * (101 / 100)^2 := by
  rw [show (301 : ℝ) - 1 = 300 by norm_num, example_small_root]
  nlinarith only [example_large_root_square, example_large_root_upper]

lemma example_dual_two :
    (Real.sqrt ((101 / 100 : ℝ) - 1) + 2 * Real.sqrt ((301 : ℝ) - 1))^2 ≤
      (101 / 100 : ℝ) * 301^2 := by
  rw [show (301 : ℝ) - 1 = 300 by norm_num, example_small_root]
  nlinarith only [example_large_root_square, example_large_root_upper]

lemma example_forward_three_fails :
    (301 : ℝ) * (101 / 100)^3 <
      (Real.sqrt ((301 : ℝ) - 1) + 3 * Real.sqrt ((101 / 100 : ℝ) - 1))^2 := by
  rw [show (301 : ℝ) - 1 = 300 by norm_num, example_small_root]
  nlinarith only [example_large_root_square, example_large_root_lower]

lemma example_not_region : ¬ Region 301 (101 / 100) := by
  intro hR
  have hcurve := hR.2.2.1 3 (by omega)
  have hfailure := example_forward_three_fails
  norm_num only [Nat.cast_ofNat] at hcurve
  norm_num only [Nat.cast_ofNat] at hfailure
  exact (not_lt_of_ge hcurve) hfailure

theorem two_curve_conditions_not_sufficient :
    ∃ x y : ℝ, 1 < x ∧ 1 < y ∧ 1 < (x-1)*(y-1) ∧
      (Real.sqrt (x-1) + 2 * Real.sqrt (y-1))^2 ≤ x*y^2 ∧
      (Real.sqrt (y-1) + 2 * Real.sqrt (x-1))^2 ≤ y*x^2 ∧
      ¬ Region x y := by
  exact ⟨301, 101/100, example_parameters_gt_one.1, example_parameters_gt_one.2,
    example_shifted_product_gt_one, example_forward_two, example_dual_two, example_not_region⟩

private lemma three_power_bound (k : ℕ) (hk : 2 ≤ k) :
    2 * ((k : ℝ) + 1)^2 ≤ 3 * (3 : ℝ)^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hpoly : 2 * ((k : ℝ) + 2)^2 ≤ 3 * (2 * ((k : ℝ) + 1)^2) := by
      nlinarith only [hk', sq_nonneg (k : ℝ)]
    calc
      2 * (((k + 1 : ℕ) : ℝ) + 1)^2
          ≤ 3 * (2 * ((k : ℝ) + 1)^2) := by
            simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hpoly
      _ ≤ 3 * (3 * (3 : ℝ)^k) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 3 * (3 : ℝ)^(k + 1) := by rw [pow_succ]; ring

/-- The known Jackson point is a nonvacuity check for the parameter region. -/
theorem region_three_three : Region 3 3 := by
  have hcurve (k : ℕ) (hk : 2 ≤ k) :
      (Real.sqrt ((3 : ℝ) - 1) + (k : ℝ) * Real.sqrt ((3 : ℝ) - 1))^2 ≤
        3 * (3 : ℝ)^k := by
    have hroot : (Real.sqrt ((3 : ℝ) - 1))^2 = 2 := by
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    calc
      _ = ((k : ℝ) + 1)^2 * (Real.sqrt ((3 : ℝ) - 1))^2 := by ring
      _ = 2 * ((k : ℝ) + 1)^2 := by rw [hroot]; ring
      _ ≤ 3 * (3 : ℝ)^k := three_power_bound k hk
  exact ⟨by norm_num, by norm_num, hcurve, hcurve⟩

end AsymmetricTutte
