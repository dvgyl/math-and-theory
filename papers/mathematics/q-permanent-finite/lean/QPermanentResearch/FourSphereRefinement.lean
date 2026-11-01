import QPermanentResearch.FourSphereConstants

/-!
A new standard-kernel scalar certificate for the refined rank-four family.
The old 256-limit family and its proofs remain unchanged. Here t = 904 and
anisotropy tau = 9999 / 10000. The analytic saddle and integration arguments
are conventional; this module verifies their scalar bounds on 444 <= k <= 446.
-/

namespace QPermanentResearch

noncomputable def fourSphereRefinedScoreFloor (k : ℝ) : ℝ :=
  (9999 / 10000 : ℝ)^2 *
    (2 * fourSphereGiniFloor k ^ 2 +
      8 * fourSphereDeletedMass k * fourSphereRadiusFloor k ^ 2 +
      fourSphereDeletedMass k ^ 2)

theorem fourSphereRefined_log_bounds {k : ℝ} (hk : 444 ≤ k) (hk' : k ≤ 446) :
    6 < Real.log (1 + k) ∧ Real.log (1 + k) < 7 := by
  have hkpos : 0 < 1 + k := by linarith
  have hexpl : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hexpu : Real.exp 1 < (11 / 4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hexp6 : Real.exp (6 : ℝ) < 445 := by
    have hpow := pow_lt_pow_left₀ hexpu (Real.exp_nonneg 1) (show (6 : ℕ) ≠ 0 by decide)
    have heq : Real.exp (6 : ℝ) = (Real.exp 1)^6 := by
      simpa using Real.exp_nat_mul (1 : ℝ) 6
    rw [heq]
    norm_num at hpow ⊢
    linarith
  have hexp7 : (447 : ℝ) < Real.exp 7 := by
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

theorem fourSphereRefined_deleted_mass_bounds {k : ℝ} (hk : 444 ≤ k) (hk' : k ≤ 446) :
    (6 / 446 : ℝ) < fourSphereDeletedMass k ∧
      fourSphereDeletedMass k < 7 / 444 := by
  have hkp : 0 < k := by linarith
  have hl := fourSphereRefined_log_bounds hk hk'
  unfold fourSphereDeletedMass
  constructor
  · apply (lt_div_iff₀ hkp).2
    linarith
  · apply (div_lt_iff₀ hkp).2
    linarith

theorem fourSphereRefined_sqrt_bounds {k : ℝ} (hk : 444 ≤ k) (hk' : k ≤ 446) :
    (2109 / 100 : ℝ) < Real.sqrt (1 + k) ∧ Real.sqrt (1 + k) < 423 / 20 := by
  have hkp : 0 ≤ 1 + k := by linarith
  have hn := Real.sqrt_nonneg (1 + k)
  have hs := Real.sq_sqrt hkp
  constructor <;> nlinarith

theorem fourSphereRefined_gini_floor_gt {k : ℝ} (hk : 444 ≤ k) (hk' : k ≤ 446) :
    (45552433 / 65120000 : ℝ) < fourSphereGiniFloor k := by
  have hkp : 0 < k := by linarith
  have hd := fourSphereRefined_deleted_mass_bounds hk hk'
  have hs := (fourSphereRefined_sqrt_bounds hk hk').2
  have hp : (31415 / 10000 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
  have hloss : 2 * Real.sqrt (1 + k) / k < (141 / 1480 : ℝ) := by
    apply (div_lt_iff₀ hkp).2
    linarith
  have hm : 0 < 1 - fourSphereDeletedMass k := by linarith
  unfold fourSphereGiniFloor
  apply (lt_div_iff₀ hm).2
  linarith

theorem fourSphereRefined_radius_floor_gt {k : ℝ} (hk : 444 ≤ k) (hk' : k ≤ 446) :
    (876533 / 1961592 : ℝ) < fourSphereRadiusFloor k := by
  have hd := (fourSphereRefined_deleted_mass_bounds hk hk').2
  have hs := (fourSphereRefined_sqrt_bounds hk hk').1
  have hsp : 0 < Real.sqrt (1 + k) + 1 := by positivity
  have hi : (1 : ℝ) / (Real.sqrt (1 + k) + 1) < 100 / 2209 := by
    apply (div_lt_iff₀ hsp).2
    linarith
  unfold fourSphereRadiusFloor
  linarith

theorem fourSphereRefined_rational_certificate :
    (1 + 1 / 10000 : ℝ) < (9999 / 10000 : ℝ)^2 *
      (2 * (45552433 / 65120000 : ℝ)^2 +
        8 * (6 / 446 : ℝ) * (876533 / 1961592 : ℝ)^2 + (6 / 446 : ℝ)^2) := by
  norm_num

theorem fourSphereRefined_score_floor_gt {k : ℝ} (hk : 444 ≤ k) (hk' : k ≤ 446) :
    (1 + 1 / 10000 : ℝ) < fourSphereRefinedScoreFloor k := by
  have hc := fourSphereRefined_gini_floor_gt hk hk'
  have hr := fourSphereRefined_radius_floor_gt hk hk'
  have hd := (fourSphereRefined_deleted_mass_bounds hk hk').1
  have hc0 : 0 ≤ fourSphereGiniFloor k := by linarith
  have hr0 : 0 ≤ fourSphereRadiusFloor k := by linarith
  have hd0 : 0 ≤ fourSphereDeletedMass k := by linarith
  have hcs : (45552433 / 65120000 : ℝ)^2 ≤ fourSphereGiniFloor k ^ 2 := by nlinarith
  have hrs : (876533 / 1961592 : ℝ)^2 ≤ fourSphereRadiusFloor k ^ 2 := by nlinarith
  have hds : (6 / 446 : ℝ)^2 ≤ fourSphereDeletedMass k ^ 2 := by nlinarith
  have hmix : (6 / 446 : ℝ) * (876533 / 1961592 : ℝ)^2 ≤
      fourSphereDeletedMass k * fourSphereRadiusFloor k ^ 2 :=
    mul_le_mul hd.le hrs (by positivity) hd0
  unfold fourSphereRefinedScoreFloor
  linarith [fourSphereRefined_rational_certificate]

theorem fourSphereRefined_normalized_derivative_floor {k : ℝ}
    (hk : 444 ≤ k) (hk' : k ≤ 446) :
    (1 - fourSphereRefinedScoreFloor k) / 4 < (-1 / 40000 : ℝ) := by
  linarith [fourSphereRefined_score_floor_gt hk hk']

theorem fourSphereRefined_limit_condition : (1 : ℝ) + 904 / 4 = 227 := by norm_num

end QPermanentResearch
