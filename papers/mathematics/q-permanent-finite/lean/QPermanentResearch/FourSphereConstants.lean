import QPermanentResearch.MeanFieldConstants

/-!
A kernel-checked scalar certificate for the rank-four mean-field family.
The function below is the explicit analytic lower bound on the limiting
score; the Gaussian and concentration identities remain outside this module.
-/

namespace QPermanentResearch

noncomputable def fourSphereDeletedMass (k : ℝ) : ℝ := Real.log (1 + k) / k
noncomputable def fourSphereGiniFloor (k : ℝ) : ℝ :=
  (Real.pi / 4 - 2 * Real.sqrt (1 + k) / k) / (1 - fourSphereDeletedMass k)
noncomputable def fourSphereRadiusFloor (k : ℝ) : ℝ :=
  1 / 2 - fourSphereDeletedMass k / 2 - 1 / (Real.sqrt (1 + k) + 1)
noncomputable def fourSphereScoreFloor (k : ℝ) : ℝ :=
  (999 / 1000 : ℝ)^2 *
    (2 * fourSphereGiniFloor k ^ 2 +
      8 * fourSphereDeletedMass k * fourSphereRadiusFloor k ^ 2 +
      fourSphereDeletedMass k ^ 2)

theorem fourSphere_log_bounds {k : ℝ} (hk : 500 ≤ k) (hk' : k ≤ 510) :
    6 < Real.log (1 + k) ∧ Real.log (1 + k) < 7 := by
  have hkpos : 0 < 1 + k := by linarith
  have hexpl : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hexpu : Real.exp 1 < (11 / 4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hexp6 : Real.exp (6 : ℝ) < 501 := by
    have hpow := pow_lt_pow_left₀ hexpu (Real.exp_nonneg 1) (show (6 : ℕ) ≠ 0 by decide)
    have heq : Real.exp (6 : ℝ) = (Real.exp 1)^6 := by
      simpa using Real.exp_nat_mul (1 : ℝ) 6
    rw [heq]
    norm_num at hpow ⊢
    linarith
  have hexp7 : (511 : ℝ) < Real.exp 7 := by
    have hpow := pow_lt_pow_left₀ hexpl (by norm_num : (0 : ℝ) ≤ 5 / 2)
      (show (7 : ℕ) ≠ 0 by decide)
    have heq : Real.exp (7 : ℝ) = (Real.exp 1)^7 := by
      simpa using Real.exp_nat_mul (1 : ℝ) 7
    rw [heq]
    norm_num at hpow ⊢
    linarith
  constructor
  · apply (Real.lt_log_iff_exp_lt hkpos).2
    linarith
  · apply (Real.log_lt_iff_lt_exp hkpos).2
    linarith

theorem fourSphere_deleted_mass_bounds {k : ℝ} (hk : 500 ≤ k) (hk' : k ≤ 510) :
    (6 / 510 : ℝ) < fourSphereDeletedMass k ∧
      fourSphereDeletedMass k < 7 / 500 := by
  have hkp : 0 < k := by linarith
  have hl := fourSphere_log_bounds hk hk'
  unfold fourSphereDeletedMass
  constructor
  · apply (lt_div_iff₀ hkp).2
    linarith
  · apply (div_lt_iff₀ hkp).2
    linarith

theorem fourSphere_sqrt_bounds {k : ℝ} (hk : 500 ≤ k) (hk' : k ≤ 510) :
    22 < Real.sqrt (1 + k) ∧ Real.sqrt (1 + k) < 1131 / 50 := by
  have hkp : 0 ≤ 1 + k := by linarith
  have hn := Real.sqrt_nonneg (1 + k)
  have hs := Real.sq_sqrt hkp
  constructor <;> nlinarith

theorem fourSphere_gini_floor_gt {k : ℝ} (hk : 500 ≤ k) (hk' : k ≤ 510) :
    (295171 / 420000 : ℝ) < fourSphereGiniFloor k := by
  have hkp : 0 < k := by linarith
  have hd := fourSphere_deleted_mass_bounds hk hk'
  have hs := (fourSphere_sqrt_bounds hk hk').2
  have hp : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
  have hloss : 2 * Real.sqrt (1 + k) / k < (1131 / 12500 : ℝ) := by
    apply (div_lt_iff₀ hkp).2
    linarith
  have hm : 0 < 1 - fourSphereDeletedMass k := by linarith
  unfold fourSphereGiniFloor
  apply (lt_div_iff₀ hm).2
  linarith

theorem fourSphere_radius_floor_gt {k : ℝ} (hk : 500 ≤ k) (hk' : k ≤ 510) :
    (10339 / 23000 : ℝ) < fourSphereRadiusFloor k := by
  have hd := (fourSphere_deleted_mass_bounds hk hk').2
  have hs := (fourSphere_sqrt_bounds hk hk').1
  have hsp : 0 < Real.sqrt (1 + k) + 1 := by positivity
  have hi : (1 : ℝ) / (Real.sqrt (1 + k) + 1) < 1 / 23 := by
    apply (div_lt_iff₀ hsp).2
    linarith
  unfold fourSphereRadiusFloor
  linarith

theorem fourSphere_rational_certificate :
    (1 + 1 / 250 : ℝ) < (999 / 1000 : ℝ)^2 *
      (2 * (295171 / 420000 : ℝ)^2 +
        8 * (6 / 510 : ℝ) * (10339 / 23000 : ℝ)^2 + (6 / 510 : ℝ)^2) := by
  norm_num

theorem fourSphere_score_floor_gt {k : ℝ} (hk : 500 ≤ k) (hk' : k ≤ 510) :
    (1 + 1 / 250 : ℝ) < fourSphereScoreFloor k := by
  have hc := fourSphere_gini_floor_gt hk hk'
  have hr := fourSphere_radius_floor_gt hk hk'
  have hd := (fourSphere_deleted_mass_bounds hk hk').1
  have hc0 : 0 ≤ fourSphereGiniFloor k := by linarith
  have hr0 : 0 ≤ fourSphereRadiusFloor k := by linarith
  have hd0 : 0 ≤ fourSphereDeletedMass k := by linarith
  have hcs : (295171 / 420000 : ℝ)^2 ≤ fourSphereGiniFloor k ^ 2 := by nlinarith
  have hrs : (10339 / 23000 : ℝ)^2 ≤ fourSphereRadiusFloor k ^ 2 := by nlinarith
  have hds : (6 / 510 : ℝ)^2 ≤ fourSphereDeletedMass k ^ 2 := by nlinarith
  have hmix : (6 / 510 : ℝ) * (10339 / 23000 : ℝ)^2 ≤
      fourSphereDeletedMass k * fourSphereRadiusFloor k ^ 2 :=
    mul_le_mul hd.le hrs (by positivity) hd0
  unfold fourSphereScoreFloor
  linarith [fourSphere_rational_certificate]

theorem fourSphere_normalized_derivative_floor {k : ℝ}
    (hk : 500 ≤ k) (hk' : k ≤ 510) :
    (1 - fourSphereScoreFloor k) / 4 < (-1 / 1000 : ℝ) := by
  linarith [fourSphere_score_floor_gt hk hk']

theorem fourSphere_limit_condition : (1 : ℝ) + 1020 / 4 = 256 := by norm_num

end QPermanentResearch
