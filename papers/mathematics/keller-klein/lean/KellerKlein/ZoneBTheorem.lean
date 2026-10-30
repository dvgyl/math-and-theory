import KellerKlein.ZoneBDecomposition
import KellerKlein.ZoneBClosure
import KellerKlein.ZoneBAliasCompensation
import KellerKlein.GaussianError
import KellerKlein.PrawitzEnvelope

noncomputable section

open scoped BigOperators

namespace KellerKlein

set_option maxHeartbeats 800000

def zoneBCommon (a x : ℝ) : ℝ :=
  a*phi x-c a-a^2*x*phi x/3+a^2*x*gaussianD x/Real.pi^2+
    a^3*gaussianN x/(3*Real.pi^2)

def zoneBAliasRemainder (a ξ : ℝ) : ℝ :=
  phi0^2/2*(ξ+ZoneB.eta)^2*a^4+6/Real.pi^4*(ξ+1)*a^4

lemma gaussianBaselineValue_eq_common (a x : ℝ) :
    gaussianBaselineValue a x-c x-c a = zoneBCommon a x-a^2/Real.pi^2 := by
  dsimp [gaussianBaselineValue, zoneBCommon]
  rw [gaussianM_eq]
  ring

lemma JUpper_le_master_base {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100)
    (hx : 0 ≤ x) :
    JUpper a x-c x-c a ≤ zoneBCommon a x+primaryLoss a (x/a)+
      zoneBAliasRemainder a (x/a)+a^4/40 := by
  have ha2 : a ≤ 1/2 := by linarith
  have hd := JUpper_le_gaussian_primary_alias ha ha2 hx
  have he := scaledGaussianKernelIntegral_le (x := x) ha ha2
  have hcoef : a^2/(2*Real.pi) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hg := gaussian_nonneg (1/a)
  have hm := mul_le_mul_of_nonneg_right hcoef hg
  have he' : scaledGaussianKernelIntegral a x ≤ gaussianBaselineValue a x+
      a^4/(15*Real.pi)+2*gaussian (1/a) := by nlinarith only [he, hm]
  have hJ : JUpper a x-c x-c a ≤ (gaussianBaselineValue a x-c x-c a)+
      primaryLoss a (x/a)+zoneBAliasIntegral a (x/a)+
      (a^4/(15*Real.pi)+9*gaussian (1/a)) := by
    linarith only [hd, he', hg]
  rw [gaussianBaselineValue_eq_common] at hJ
  have hAlias : zoneBAliasIntegral a (x/a)-a^2/Real.pi^2 ≤
      zoneBAliasRemainder a (x/a) := by
    convert zoneBAliasIntegral_compensated ha (div_nonneg hx ha.le) using 1 <;>
      dsimp [zoneBAliasRemainder, ZoneB.eta, zoneBAliasEta] <;> ring
  have hBudget := gaussian_remainder_budget ha haMax
  linarith only [hJ, hAlias, hBudget]

lemma JUpper_le_masterSmall {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100)
    (hx : 0 ≤ x) : JUpper a x-c x-c a ≤ ZoneB.masterSmall a x := by
  have hb := JUpper_le_master_base ha haMax hx
  have hp := primaryLoss_le_small ha (div_nonneg hx ha.le)
  have he : phi0*(5*a^5/4+21*a^7/4)*kernelLossCoeff (x/a) =
      phi0*(5*a^3/4+21*a^5/4)*(x^2/2+x^3/(6*a)+a*x/2) := by
    dsimp [kernelLossCoeff]
    field_simp [ha.ne']
    ring
  rw [he] at hp
  dsimp [zoneBCommon, zoneBAliasRemainder] at hb
  dsimp [ZoneB.masterSmall]
  linarith only [hb, hp]

lemma JUpper_le_masterLarge {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100)
    (hx : 0 ≤ x) : JUpper a x-c x-c a ≤ ZoneB.masterLarge a x := by
  have hb := JUpper_le_master_base ha haMax hx
  have hp := primaryLoss_le_large ha (div_nonneg hx ha.le)
  dsimp [zoneBCommon, zoneBAliasRemainder] at hb
  dsimp [ZoneB.masterLarge]
  linarith only [hb, hp]

theorem JUpper_le_c_pair_of_zoneB {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100)
    (hxlo : a/2 ≤ x) (hax : a*x^2 ≤ 1) : JUpper a x ≤ c x+c a := by
  have hx : 0 ≤ x := by linarith
  by_cases hx1 : x ≤ 1
  · have hmaster := (JUpper_le_masterSmall ha haMax hx).trans
      (ZoneB.masterSmall_le ha haMax hxlo hx1)
    have hφ0 := phi0_pos.le
    have hpos : 0 ≤ phi0*a^3/20 := by positivity
    linarith
  · have hmaster := (JUpper_le_masterLarge ha haMax hx).trans
      (ZoneB.masterLarge_le ha haMax (le_of_not_ge hx1) hax)
    linarith

theorem rademacher_concentration_zoneB {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100) (hc : ∀ i, 0 ≤ coeff i)
    (hca : ∀ i, coeff i ≤ a) (hvar : ∑ i, coeff i^2 = 1) (hxlo : a/2 ≤ x) :
    rademacherConcentration coeff x ≤ H a+H x := by
  have hx : 0 ≤ x := by linarith
  by_cases hax : a*x^2 ≤ 1
  · have hJ := JUpper_le_c_pair_of_zoneB ha haMax hxlo hax
    have hp := rademacher_concentration_le_JUpper coeff ha (by linarith) hc hca hvar hx
    dsimp [H]
    linarith
  · have hH := one_le_H_add_H_of_large ha haMax hx (le_of_not_ge hax)
    have hp : rademacherConcentration coeff x ≤ 1 := cubeProbability_le_one _
    linarith

/-- The full missing small-maximum-coefficient concentration half, for the
actual finite Rademacher law and every nonnegative location. -/
theorem rademacher_concentration_small_max {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100) (hc : ∀ i, 0 ≤ coeff i)
    (hca : ∀ i, coeff i ≤ a) (hvar : ∑ i, coeff i^2 = 1) (hx : 0 ≤ x) :
    rademacherConcentration coeff x ≤ H a+H x := by
  rcases le_total x (a/2) with hsmall | hlarge
  · exact rademacher_concentration_zoneA coeff ha haMax hc hca hvar hx hsmall
  · exact rademacher_concentration_zoneB coeff ha haMax hc hca hvar hlarge

theorem rademacherCDF_small_max_nonneg {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100) (hc : ∀ i, 0 ≤ coeff i)
    (hca : ∀ i, coeff i ≤ a) (hvar : ∑ i, coeff i^2 = 1) (hx : 0 ≤ x) :
    rademacherCDF coeff x ≤ 1/2+c x+c a := by
  have hp := rademacher_concentration_small_max coeff ha haMax hc hca hvar hx
  have hs := rademacherCDF_symmetry coeff x
  have hc0 := rademacherConcentration_eq_one_sub_two_strictCDF coeff hx
  unfold H at hp
  linarith

end KellerKlein
