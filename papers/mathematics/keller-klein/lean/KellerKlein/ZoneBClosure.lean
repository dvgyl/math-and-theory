import KellerKlein.GaussianFourier
import KellerKlein.GaussianTarget
import KellerKlein.ZoneAConstants
import KellerKlein.ZoneAProfile

set_option maxHeartbeats 1000000

namespace KellerKlein.ZoneB

noncomputable section

def eta : ℝ := 1 / 2 + 3 / Real.pi ^ 2

def masterSmall (a x : ℝ) : ℝ :=
  a * phi x - c a - a ^ 2 * x * phi x / 3 +
  a ^ 2 * x * gaussianD x / Real.pi ^ 2 + a ^ 3 * gaussianN x / (3 * Real.pi ^ 2) +
  phi0 * (5 * a ^ 3 / 4 + 21 * a ^ 5 / 4) * (x ^ 2 / 2 + x ^ 3 / (6 * a) + a * x / 2) +
  phi0 ^ 2 / 2 * (x / a + eta) ^ 2 * a ^ 4 +
  6 / Real.pi ^ 4 * (x / a + 1) * a ^ 4 + a ^ 4 / 40

def masterLarge (a x : ℝ) : ℝ :=
  a * phi x - c a - a ^ 2 * x * phi x / 3 +
  a ^ 2 * x * gaussianD x / Real.pi ^ 2 + a ^ 3 * gaussianN x / (3 * Real.pi ^ 2) +
  (phi0 * a ^ 3 / 4 + a ^ 2 / (6 * Real.pi) + 3 * phi0 * a ^ 5 / 4 +
    2 * a ^ 4 / (5 * Real.pi)) +
  phi0 ^ 2 / 2 * (x / a + eta) ^ 2 * a ^ 4 +
  6 / Real.pi ^ 4 * (x / a + 1) * a ^ 4 + a ^ 4 / 40

def C2 : ℝ := 100 / 351 + 1 / 5
def C1 : ℝ := 400 / 1053 + 1 / 3
def C0 : ℝ := 5 / 36 + 200 / 1053 + 5 / 78
def K : ℝ := 32 / 25

def smallPolynomial (a ξ : ℝ) : ℝ :=
  1 / 6 - ξ ^ 2 / 2 - ξ / 3 +
    a ^ 2 * (ξ ^ 4 / 8 + ξ ^ 3 / 6 + K * (ξ ^ 2 / 2 + ξ ^ 3 / 6 + ξ / 2)) +
    a * (C2 * ξ ^ 2 + C1 * ξ + C0)

def largeRemainder (a : ℝ) : ℝ :=
  a ^ 2 / 15 + 2 * a / 9 + 2 * a ^ 2 / 45 +
    (a ^ 2 / 10 + a / 18 + 3 * a ^ 4 / 10 + 2 * a ^ 3 / 15) +
    (2 / 25) * (1 + 5 * a / 3 + 25 * a ^ 3 / 36) +
    (2 / 27) * (a + a ^ 3) + a ^ 3 / 40

lemma phi_upper_quartic (x : ℝ) :
    phi x ≤ phi0 * (1 - x ^ 2 / 2 + x ^ 4 / 8) := by
  have hh := ZoneA.exp_neg_le_quadratic (show 0 ≤ x ^ 2 / 2 by positivity)
  have hm := mul_le_mul_of_nonneg_right hh phi0_pos.le
  unfold phi gaussian
  simp only [neg_div] at hm ⊢
  nlinarith only [hm]

lemma eta_nonneg : 0 ≤ eta := by unfold eta; positivity

lemma eta_le : eta ≤ (5 / 6 : ℝ) := by
  unfold eta
  have h : (3 : ℝ) / Real.pi ^ 2 ≤ 1 / 3 :=
    (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr (by nlinarith [ZoneA.pi_sq_lower])
  linarith

lemma inv_pi_sq_le_scaled_phi0 : (1 : ℝ) / Real.pi ^ 2 ≤ (100 / 351) * phi0 := by
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  have h : (9 : ℝ) * (39 / 100) ≤ Real.pi ^ 2 * phi0 :=
    mul_le_mul ZoneA.pi_sq_lower ZoneA.phi0_lower (by norm_num) (sq_nonneg _)
  nlinarith only [h]

lemma two_div_three_pi_sq_le_scaled_phi0 :
    (2 : ℝ) / (3 * Real.pi ^ 2) ≤ (200 / 1053) * phi0 := by
  apply (div_le_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2)).mpr
  have h : (9 : ℝ) * (39 / 100) ≤ Real.pi ^ 2 * phi0 :=
    mul_le_mul ZoneA.pi_sq_lower ZoneA.phi0_lower (by norm_num) (sq_nonneg _)
  nlinarith only [h]

lemma six_div_pi_fourth_le_scaled_phi0 :
    (6 : ℝ) / Real.pi ^ 4 ≤ (200 / 1053) * phi0 := by
  apply (div_le_iff₀ (by positivity : 0 < Real.pi ^ 4)).mpr
  have hp : (81 : ℝ) ≤ Real.pi ^ 4 := by
    nlinarith [ZoneA.pi_sq_lower, sq_nonneg (Real.pi ^ 2 - 9)]
  have h : (81 : ℝ) * (39 / 100) ≤ Real.pi ^ 4 * phi0 :=
    mul_le_mul hp ZoneA.phi0_lower (by norm_num) (pow_nonneg Real.pi_pos.le _)
  nlinarith only [h]

lemma smallPolynomial_le {a ξ : ℝ} (ha : 0 ≤ a) (ha7 : a ≤ 7 / 100)
    (hξ : 1 / 2 ≤ ξ) (hax : a * ξ ≤ 1) : smallPolynomial a ξ ≤ -(1 / 20 : ℝ) := by
  have hξ0 : 0 ≤ ξ := by linarith
  have ha2 : a ^ 2 ≤ (7 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ ha ha7 2
  have hC : 1 / 6 + a * C0 ≤ (1 / 5 : ℝ) := by
    unfold C0
    nlinarith only [ha7]
  by_cases hξ1 : ξ ≤ 1
  · have h2 : ξ ^ 2 ≤ ξ := by nlinarith [mul_nonneg hξ0 (sub_nonneg.mpr hξ1)]
    have h3 : ξ ^ 3 ≤ ξ ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg ξ) (sub_nonneg.mpr hξ1)]
    have h4 : ξ ^ 4 ≤ ξ ^ 2 := by
      have hh := pow_le_pow_left₀ (sq_nonneg ξ) h2 2
      nlinarith only [hh]
    have hh4 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ a ^ 2 / 8 by positivity)
    have hh3 := mul_le_mul_of_nonneg_left (h3.trans h2) (show 0 ≤ a ^ 2 / 6 by positivity)
    have hhK := mul_le_mul_of_nonneg_left h3 (show 0 ≤ a ^ 2 * K / 6 by unfold K; positivity)
    have hP : smallPolynomial a ξ ≤
        (1 / 6 + a * C0) + (-1 / 2 + a * C2 + a ^ 2 * (1 / 8 + 2 * K / 3)) * ξ ^ 2 +
          (-1 / 3 + a * C1 + a ^ 2 * (1 / 6 + K / 2)) * ξ := by
      unfold smallPolynomial
      nlinarith only [hh4, hh3, hhK]
    have hQ : -1 / 2 + a * C2 + a ^ 2 * (1 / 8 + 2 * K / 3) ≤ -(9 / 20 : ℝ) := by
      unfold C2 K
      nlinarith only [ha7, ha2]
    have hL : -1 / 3 + a * C1 + a ^ 2 * (1 / 6 + K / 2) ≤ -(11 / 40 : ℝ) := by
      unfold C1 K
      nlinarith only [ha7, ha2]
    have hQm := mul_le_mul_of_nonneg_right hQ (sq_nonneg ξ)
    have hLm := mul_le_mul_of_nonneg_right hL hξ0
    have hξ2 : (1 / 2 : ℝ) ^ 2 ≤ ξ ^ 2 := pow_le_pow_left₀ (by norm_num) hξ 2
    nlinarith only [hP, hQm, hLm, hC, hξ, hξ2]
  · have hξ1' : 1 ≤ ξ := le_of_not_ge hξ1
    have hax2 : a ^ 2 * ξ ^ 2 ≤ 1 := by
      have hh := pow_le_pow_left₀ (mul_nonneg ha hξ0) hax 2
      simpa only [mul_pow, one_pow] using hh
    have h4 : a ^ 2 * ξ ^ 4 ≤ ξ ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hax2 (sq_nonneg ξ)
      nlinarith only [hh]
    have h3 : a ^ 2 * ξ ^ 3 ≤ ξ := by
      have hh := mul_le_mul_of_nonneg_right hax2 hξ0
      nlinarith only [hh]
    have hK3 : a ^ 2 * ξ ^ 3 ≤ a * ξ ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hax (show 0 ≤ a * ξ ^ 2 by positivity)
      nlinarith only [hh]
    have hhK := mul_le_mul_of_nonneg_left hK3 (show 0 ≤ K / 6 by unfold K; norm_num)
    have hP : smallPolynomial a ξ ≤
        (1 / 6 + a * C0) + (-3 / 8 + a * C2 + K * (a ^ 2 / 2 + a / 6)) * ξ ^ 2 +
          (-1 / 6 + a * C1 + K * a ^ 2 / 2) * ξ := by
      unfold smallPolynomial
      nlinarith only [h4, h3, hhK]
    have hQ : -3 / 8 + a * C2 + K * (a ^ 2 / 2 + a / 6) ≤ -(3 / 10 : ℝ) := by
      unfold C2 K
      nlinarith only [ha7, ha2]
    have hL : -1 / 6 + a * C1 + K * a ^ 2 / 2 ≤ -(1 / 10 : ℝ) := by
      unfold C1 K
      nlinarith only [ha7, ha2]
    have hQm := mul_le_mul_of_nonneg_right hQ (sq_nonneg ξ)
    have hLm := mul_le_mul_of_nonneg_right hL hξ0
    have hξ2 : (1 : ℝ) ≤ ξ ^ 2 := by nlinarith [sq_nonneg (ξ - 1)]
    nlinarith only [hP, hQm, hLm, hC, hξ1', hξ2]

lemma largeRemainder_le {a : ℝ} (ha : 0 ≤ a) (ha7 : a ≤ 7 / 100) :
    largeRemainder a < (117 / 800 : ℝ) - 1 / 40 := by
  calc
    largeRemainder a ≤ largeRemainder (7 / 100) := by
      unfold largeRemainder
      gcongr
    _ < (117 / 800 : ℝ) - 1 / 40 := by norm_num [largeRemainder]

lemma masterSmall_scaled_le {a ξ : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100)
    (hξ : 0 ≤ ξ) (hax : a * ξ ≤ 1) :
    masterSmall a (a * ξ) ≤ phi0 * a ^ 3 * smallPolynomial a ξ := by
  have hx : 0 ≤ a * ξ := mul_nonneg ha.le hξ
  have hcu := mul_le_mul_of_nonneg_left (phi_upper_quartic (a * ξ)) ha.le
  have hcl := mul_le_mul_of_nonneg_left (phi_lower_quadratic (a * ξ))
    (show 0 ≤ a ^ 2 * (a * ξ) / 3 by positivity)
  have hca := c_lower_cubic ha.le
  have hnormal : a * phi (a * ξ) - c a - a ^ 2 * (a * ξ) * phi (a * ξ) / 3 ≤
      phi0 * a ^ 3 * (1 / 6 - ξ ^ 2 / 2 - ξ / 3 + a ^ 2 * (ξ ^ 4 / 8 + ξ ^ 3 / 6)) := by
    nlinarith only [hcu, hcl, hca]
  have hdg := mul_le_mul_of_nonneg_left (gaussianD_le_self hx) hx
  have hd1 := div_le_div_of_nonneg_right hdg (sq_nonneg Real.pi)
  have hd2 := mul_le_mul_of_nonneg_left hd1 (sq_nonneg a)
  have hd3 := mul_le_mul_of_nonneg_right inv_pi_sq_le_scaled_phi0
    (show 0 ≤ a ^ 4 * ξ ^ 2 by positivity)
  have hd : a ^ 2 * (a * ξ) * gaussianD (a * ξ) / Real.pi ^ 2 ≤
      phi0 * a ^ 3 * (a * (100 / 351) * ξ ^ 2) := by
    calc
      _ = a ^ 2 * ((a * ξ) * gaussianD (a * ξ) / Real.pi ^ 2) := by ring
      _ ≤ a ^ 2 * ((a * ξ) ^ 2 / Real.pi ^ 2) := by
        convert hd2 using 1 <;> ring
      _ = (1 / Real.pi ^ 2) * (a ^ 4 * ξ ^ 2) := by ring
      _ ≤ (100 / 351) * phi0 * (a ^ 4 * ξ ^ 2) := hd3
      _ = _ := by ring
  have hn1 := div_le_div_of_nonneg_right (gaussianN_le_two_mul hx hax)
    (show 0 ≤ 3 * Real.pi ^ 2 by positivity)
  have hn2 := mul_le_mul_of_nonneg_left hn1 (pow_nonneg ha.le 3)
  have hn3 := mul_le_mul_of_nonneg_right two_div_three_pi_sq_le_scaled_phi0
    (show 0 ≤ a ^ 4 * ξ by positivity)
  have hn : a ^ 3 * gaussianN (a * ξ) / (3 * Real.pi ^ 2) ≤
      phi0 * a ^ 3 * (a * (200 / 1053) * ξ) := by
    calc
      _ = a ^ 3 * (gaussianN (a * ξ) / (3 * Real.pi ^ 2)) := by ring
      _ ≤ a ^ 3 * (2 * (a * ξ) / (3 * Real.pi ^ 2)) := hn2
      _ = (2 / (3 * Real.pi ^ 2)) * (a ^ 4 * ξ) := by ring
      _ ≤ (200 / 1053) * phi0 * (a ^ 4 * ξ) := hn3
      _ = _ := by ring
  have ha2 : a ^ 2 ≤ (7 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ ha.le ha7 2
  have hK : 5 / 4 + 21 * a ^ 2 / 4 ≤ K := by unfold K; nlinarith only [ha2]
  have hKm := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ phi0 * a ^ 5 * (ξ ^ 2 / 2 + ξ ^ 3 / 6 + ξ / 2) by
      have := phi0_pos; positivity)
  have hds : (a * ξ) ^ 2 / 2 + (a * ξ) ^ 3 / (6 * a) + a * (a * ξ) / 2 =
      a ^ 2 * (ξ ^ 2 / 2 + ξ ^ 3 / 6 + ξ / 2) := by
    field_simp [ha.ne']
    ring
  have hsmall : phi0 * (5 * a ^ 3 / 4 + 21 * a ^ 5 / 4) *
      ((a * ξ) ^ 2 / 2 + (a * ξ) ^ 3 / (6 * a) + a * (a * ξ) / 2) ≤
      phi0 * a ^ 3 * (a ^ 2 * K * (ξ ^ 2 / 2 + ξ ^ 3 / 6 + ξ / 2)) := by
    rw [hds]
    nlinarith only [hKm]
  have hηsq : (ξ + eta) ^ 2 ≤ (ξ + 5 / 6) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg hξ eta_nonneg) (add_le_add_left eta_le ξ) 2
  have hph : phi0 / 2 ≤ (1 / 5 : ℝ) := by linarith [ZoneA.phi0_upper]
  have hq := mul_le_mul hph hηsq (sq_nonneg _) (by norm_num : 0 ≤ (1 / 5 : ℝ))
  have hqm := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ phi0 * a ^ 4 by have := phi0_pos; positivity)
  have halias : phi0 ^ 2 / 2 * (ξ + eta) ^ 2 * a ^ 4 ≤
      phi0 * a ^ 3 * (a * (ξ ^ 2 / 5 + ξ / 3 + 5 / 36)) := by
    nlinarith only [hqm]
  have hb0 := mul_le_mul_of_nonneg_right six_div_pi_fourth_le_scaled_phi0
    (show 0 ≤ (ξ + 1) * a ^ 4 by positivity)
  have hb : 6 / Real.pi ^ 4 * (ξ + 1) * a ^ 4 ≤
      phi0 * a ^ 3 * (a * (200 / 1053) * (ξ + 1)) := by
    nlinarith only [hb0]
  have hr0 : (1 / 40 : ℝ) ≤ (5 / 78) * phi0 := by linarith [ZoneA.phi0_lower]
  have hr1 := mul_le_mul_of_nonneg_right hr0 (pow_nonneg ha.le 4)
  have hr : a ^ 4 / 40 ≤ phi0 * a ^ 3 * (a * (5 / 78)) := by
    nlinarith only [hr1]
  have hdiv : a * ξ / a = ξ := by field_simp
  unfold masterSmall smallPolynomial C0 C1 C2
  rw [hdiv]
  nlinarith only [hnormal, hd, hn, hsmall, halias, hb, hr]

/-- Actual small-x master closure for the audited Gaussian functions. -/
theorem masterSmall_le {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100)
    (hxlo : a / 2 ≤ x) (hx1 : x ≤ 1) :
    masterSmall a x ≤ -phi0 * a ^ 3 / 20 := by
  have hξ : (1 / 2 : ℝ) ≤ x / a := (le_div_iff₀ ha).mpr (by linarith)
  have heq : a * (x / a) = x := by field_simp
  have hax : a * (x / a) ≤ 1 := by rwa [heq]
  have hm := masterSmall_scaled_le ha ha7 (show 0 ≤ x / a by linarith) hax
  rw [heq] at hm
  have hp := smallPolynomial_le ha.le ha7 hξ hax
  have hpm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ phi0 * a ^ 3 by have := phi0_pos; positivity)
  nlinarith only [hm, hpm]

lemma phi_gap_large {x : ℝ} (hx : 1 ≤ x) : phi x - phi0 ≤ -(117 / 800 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hexp : Real.exp (-(1 / 2 : ℝ)) ≤ (5 / 8 : ℝ) := by
    rw [Real.exp_neg]
    have hh : 1 / Real.exp (1 / 2 : ℝ) ≤ (5 / 8 : ℝ) := by
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      linarith
    simpa only [one_div] using hh
  have hsq : (1 : ℝ) ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hg : gaussian x ≤ (5 / 8 : ℝ) := by
    apply le_trans _ hexp
    apply Real.exp_le_exp.mpr
    nlinarith
  have hgm := mul_le_mul_of_nonneg_right hg phi0_pos.le
  unfold phi
  linarith [ZoneA.phi0_lower]

lemma gaussianN_scaled_large (x : ℝ) : gaussianN x / (3 * Real.pi ^ 2) ≤ (2 / 45 : ℝ) := by
  apply (div_le_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2)).mpr
  have hN := (abs_le.mp (abs_gaussianN_le x)).2
  have hφ := mul_le_mul_of_nonneg_left ZoneA.phi0_upper Real.pi_pos.le
  have hp := mul_nonneg Real.pi_pos.le (show 0 ≤ Real.pi - 3 by linarith [Real.pi_gt_three])
  nlinarith

/-- Actual large-x master closure; the cutoff hypothesis is precisely a*x²≤1. -/
theorem masterLarge_le {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100)
    (hx : 1 ≤ x) (hax2 : a * x ^ 2 ≤ 1) : masterLarge a x ≤ -a / 40 := by
  have hx0 : 0 ≤ x := by linarith
  have hxx : x ≤ x ^ 2 := by nlinarith [mul_nonneg hx0 (show 0 ≤ x - 1 by linarith)]
  have hax : a * x ≤ 1 := (mul_le_mul_of_nonneg_left hxx ha.le).trans hax2
  have haxm := mul_le_mul_of_nonneg_left hax (sq_nonneg a)
  have hφg := mul_le_mul_of_nonneg_left (phi_gap_large hx) ha.le
  have hca := c_lower_cubic ha.le
  have hφ3 := mul_le_mul_of_nonneg_right ZoneA.phi0_upper (pow_nonneg ha.le 3)
  have hnormal : a * phi x - c a ≤ -(117 / 800) * a + a ^ 3 / 15 := by
    nlinarith only [hφg, hca, hφ3]
  have hnegative : 0 ≤ a ^ 2 * x * phi x :=
    mul_nonneg (mul_nonneg (sq_nonneg a) hx0) (phi_pos x).le
  have hDcoef : x * gaussianD x / Real.pi ^ 2 ≤ (2 / 9 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [mul_gaussianD_le_two x, ZoneA.pi_sq_lower]
  have hD0 := mul_le_mul_of_nonneg_left hDcoef (sq_nonneg a)
  have hd : a ^ 2 * x * gaussianD x / Real.pi ^ 2 ≤ 2 * a ^ 2 / 9 := by
    convert hD0 using 1 <;> ring
  have hN0 := mul_le_mul_of_nonneg_left (gaussianN_scaled_large x) (pow_nonneg ha.le 3)
  have hn : a ^ 3 * gaussianN x / (3 * Real.pi ^ 2) ≤ 2 * a ^ 3 / 45 := by
    convert hN0 using 1 <;> ring
  have hinv6 : (1 : ℝ) / (6 * Real.pi) ≤ 1 / 18 := by
    apply (div_le_iff₀ (by positivity : 0 < 6 * Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hinv5 : (2 : ℝ) / (5 * Real.pi) ≤ 2 / 15 := by
    apply (div_le_iff₀ (by positivity : 0 < 5 * Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hv2 := mul_le_mul_of_nonneg_right hinv6 (sq_nonneg a)
  have hv4 := mul_le_mul_of_nonneg_right hinv5 (pow_nonneg ha.le 4)
  have hv5 := mul_le_mul_of_nonneg_right ZoneA.phi0_upper (pow_nonneg ha.le 5)
  have hv2' : a ^ 2 / (6 * Real.pi) ≤ a ^ 2 / 18 := by
    convert hv2 using 1 <;> ring
  have hv4' : 2 * a ^ 4 / (5 * Real.pi) ≤ 2 * a ^ 4 / 15 := by
    convert hv4 using 1 <;> ring
  have hDlarge : phi0 * a ^ 3 / 4 + a ^ 2 / (6 * Real.pi) +
      3 * phi0 * a ^ 5 / 4 + 2 * a ^ 4 / (5 * Real.pi) ≤
      a ^ 3 / 10 + a ^ 2 / 18 + 3 * a ^ 5 / 10 + 2 * a ^ 4 / 15 := by
    nlinarith only [hφ3, hv2', hv4', hv5]
  have hη2 : eta ^ 2 ≤ (5 / 6 : ℝ) ^ 2 := pow_le_pow_left₀ eta_nonneg eta_le 2
  have hfirst := mul_le_mul_of_nonneg_left hax2 ha.le
  have hmiddle := mul_le_mul_of_nonneg_right eta_le
    (show 0 ≤ 2 * a ^ 3 * x by positivity)
  have hlast := mul_le_mul_of_nonneg_right hη2 (pow_nonneg ha.le 4)
  have hcore : a ^ 2 * x ^ 2 + 2 * eta * a ^ 3 * x + eta ^ 2 * a ^ 4 ≤
      a + 5 * a ^ 2 / 3 + 25 * a ^ 4 / 36 := by
    nlinarith only [hfirst, hmiddle, hlast, haxm]
  have hcore0 : 0 ≤ a ^ 2 * x ^ 2 + 2 * eta * a ^ 3 * x + eta ^ 2 * a ^ 4 := by
    have := eta_nonneg
    positivity
  have hφ2 := pow_le_pow_left₀ phi0_pos.le ZoneA.phi0_upper 2
  have hφhalf : phi0 ^ 2 / 2 ≤ (2 / 25 : ℝ) := by nlinarith only [hφ2]
  have hproduct := mul_le_mul hφhalf hcore hcore0 (by norm_num : 0 ≤ (2 / 25 : ℝ))
  have heq : (x / a + eta) ^ 2 * a ^ 4 =
      a ^ 2 * x ^ 2 + 2 * eta * a ^ 3 * x + eta ^ 2 * a ^ 4 := by
    field_simp [ha.ne']
    ring
  have halias : phi0 ^ 2 / 2 * (x / a + eta) ^ 2 * a ^ 4 ≤
      (2 / 25) * (a + 5 * a ^ 2 / 3 + 25 * a ^ 4 / 36) := by
    calc
      _ = phi0 ^ 2 / 2 * ((x / a + eta) ^ 2 * a ^ 4) := by ring
      _ = phi0 ^ 2 / 2 * (a ^ 2 * x ^ 2 + 2 * eta * a ^ 3 * x + eta ^ 2 * a ^ 4) := by rw [heq]
      _ ≤ _ := hproduct
  have hp4 : (81 : ℝ) ≤ Real.pi ^ 4 := by
    nlinarith [ZoneA.pi_sq_lower, sq_nonneg (Real.pi ^ 2 - 9)]
  have hbcoef : (6 : ℝ) / Real.pi ^ 4 ≤ 2 / 27 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi ^ 4)).mpr
    nlinarith only [hp4]
  have hbcore : (x / a + 1) * a ^ 4 ≤ a ^ 2 + a ^ 4 := by
    have heq : (x / a + 1) * a ^ 4 = a ^ 3 * x + a ^ 4 := by
      field_simp [ha.ne']
      ring
    rw [heq]
    nlinarith only [haxm]
  have hb0 := mul_le_mul hbcoef hbcore
    (show 0 ≤ (x / a + 1) * a ^ 4 by positivity) (by norm_num : 0 ≤ (2 / 27 : ℝ))
  have hb : 6 / Real.pi ^ 4 * (x / a + 1) * a ^ 4 ≤ (2 / 27) * (a ^ 2 + a ^ 4) := by
    nlinarith only [hb0]
  have htotal : masterLarge a x ≤ a * (-(117 / 800) + largeRemainder a) := by
    unfold masterLarge largeRemainder
    nlinarith only [hnormal, hnegative, hd, hn, hDlarge, halias, hb]
  have hR : -(117 / 800) + largeRemainder a ≤ -(1 / 40 : ℝ) :=
    by linarith [largeRemainder_le ha.le ha7]
  have hRm := mul_le_mul_of_nonneg_left hR ha.le
  nlinarith only [htotal, hRm]

end

end KellerKlein.ZoneB
