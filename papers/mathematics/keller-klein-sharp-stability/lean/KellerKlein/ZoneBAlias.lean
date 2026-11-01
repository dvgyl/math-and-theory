import KellerKlein.ZoneAScaled
import KellerKlein.ZoneAAlias
import KellerKlein.ZoneAConstants
import KellerKlein.Envelopes

noncomputable section
open Set MeasureTheory

namespace KellerKlein

def zoneBAliasPolynomial (ξ t : ℝ) : ℝ :=
  t * |Real.cos (Real.pi*ξ)| + (Real.pi*ξ+4/3)*t^2*|Real.sin (Real.pi*ξ)| +
    (4*Real.pi/3)*ξ*t^3

def zoneBAliasValue (a ξ : ℝ) : ℝ :=
  a^2/Real.pi^2*|Real.cos (Real.pi*ξ)| +
    (phi0/Real.pi)*(ξ+4/(3*Real.pi))*a^3*|Real.sin (Real.pi*ξ)| +
    8*ξ*a^4/(3*Real.pi^3)

def zoneBAliasIntegrand (a ξ s : ℝ) : ℝ :=
  |upperKernel ξ (a*s/Real.pi)| * cosineProfile a s

def zoneBAliasIntegral (a ξ : ℝ) : ℝ :=
  a/Real.pi * ∫ s in (crossoverRoot/a)..(Real.pi/a), zoneBAliasIntegrand a ξ s

lemma abs_cos_toward_bound {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    |Real.cos (β*(1-t))| ≤ |Real.cos β| + β*t*|Real.sin β| := by
  rw [show β*(1-t)=β-β*t by ring, Real.cos_sub]
  calc
    |Real.cos β*Real.cos (β*t)+Real.sin β*Real.sin (β*t)| ≤
        |Real.cos β| * |Real.cos (β*t)| + |Real.sin β| * |Real.sin (β*t)| := by
      simpa only [abs_mul] using abs_add_le
        (Real.cos β*Real.cos (β*t)) (Real.sin β*Real.sin (β*t))
    _ ≤ |Real.cos β| * 1+|Real.sin β| * (β*t) := by
      gcongr
      · exact Real.abs_cos_le_one _
      · simpa only [abs_of_nonneg (mul_nonneg hβ ht)] using
          Real.abs_sin_le_abs (x := β*t)
    _ = |Real.cos β| + β*t*|Real.sin β| := by ring

lemma abs_sin_toward_bound {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    |Real.sin (β*(1-t))| ≤ |Real.sin β| + β*t*|Real.cos β| := by
  rw [show β*(1-t)=β-β*t by ring, Real.sin_sub]
  calc
    |Real.sin β*Real.cos (β*t)-Real.cos β*Real.sin (β*t)| ≤
        |Real.sin β| * |Real.cos (β*t)| + |Real.cos β| * |Real.sin (β*t)| := by
      simpa only [abs_mul] using abs_sub
        (Real.sin β*Real.cos (β*t)) (Real.cos β*Real.sin (β*t))
    _ ≤ |Real.sin β| * 1+|Real.cos β| * (β*t) := by
      gcongr
      · exact Real.abs_cos_le_one _
      · simpa only [abs_of_nonneg (mul_nonneg hβ ht)] using
          Real.abs_sin_le_abs (x := β*t)
    _ = |Real.sin β| + β*t*|Real.cos β| := by ring

lemma rho_alias_four_thirds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1/2) :
    rho (1-t) ≤ (4/3)*t^2 := by
  have h := rho_alias_bound ht ht1
  have ht2 : t^2 ≤ 1/4 := by nlinarith
  have ht4 : t^4 ≤ t^2/4 := by nlinarith [sq_nonneg (t^2-1/4)]
  have hp : Real.pi ≤ 13/4 := le_trans Real.pi_lt_d2.le (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg t)
  nlinarith

lemma abs_upperKernel_alias_bound {ξ t : ℝ} (hξ : 0 ≤ ξ)
    (ht : 0 < t) (ht1 : t ≤ 1/2) :
    |upperKernel ξ (1-t)| ≤ zoneBAliasPolynomial ξ t := by
  have hr0 : 0 ≤ rho (1-t) := rho_nonneg (by linarith) (by linarith)
  have hr := rho_alias_four_thirds ht ht1
  have hb : 0 ≤ Real.pi*ξ := mul_nonneg Real.pi_pos.le hξ
  have hc := abs_cos_toward_bound hb ht.le
  have hs := abs_sin_toward_bound hb ht.le
  have hm := mul_le_mul hr hs (abs_nonneg _)
    (by positivity : 0 ≤ (4/3:ℝ)*t^2)
  have hn := mul_le_mul_of_nonneg_left hc ht.le
  have hlast := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (Real.pi*ξ))
    (by positivity : 0 ≤ (4*Real.pi/3)*ξ*t^3)
  calc
    |upperKernel ξ (1-t)| ≤ t*|Real.cos (Real.pi*ξ*(1-t))| +
        rho (1-t)*|Real.sin (Real.pi*ξ*(1-t))| := by
      simpa only [upperKernel, sub_sub_cancel, abs_mul, abs_of_pos ht,
        abs_of_nonneg hr0] using
        abs_add_le (t*Real.cos (Real.pi*ξ*(1-t)))
          (rho (1-t)*Real.sin (Real.pi*ξ*(1-t)))
    _ ≤ zoneBAliasPolynomial ξ t := by
      unfold zoneBAliasPolynomial
      nlinarith only [hm, hn, hlast]

lemma zoneBAliasPolynomial_nonneg {ξ t : ℝ} (hξ : 0 ≤ ξ) (ht : 0 ≤ t) :
    0 ≤ zoneBAliasPolynomial ξ t := by
  unfold zoneBAliasPolynomial
  positivity

lemma zoneBAlias_polynomial_expansion (a ξ s : ℝ) :
    zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s =
      (a/Real.pi*|Real.cos (Real.pi*ξ)|)*(s^1*gaussian s) +
      ((Real.pi*ξ+4/3)*a^2/Real.pi^2*|Real.sin (Real.pi*ξ)|)*(s^2*gaussian s) +
      ((4*Real.pi/3)*ξ*a^3/Real.pi^3)*(s^3*gaussian s) := by
  unfold zoneBAliasPolynomial
  ring

lemma integrable_zoneBAliasPolynomial (a ξ : ℝ) :
    Integrable (fun s => zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s) := by
  simp_rw [zoneBAlias_polynomial_expansion]
  exact (((integrable_pow_gaussian 1).const_mul _).add
    ((integrable_pow_gaussian 2).const_mul _)).add
    ((integrable_pow_gaussian 3).const_mul _)

lemma integral_zoneBAliasPolynomial (a ξ : ℝ) :
    a/Real.pi * (∫ s in Ioi (0 : ℝ),
      zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s) = zoneBAliasValue a ξ := by
  simp_rw [zoneBAlias_polynomial_expansion]
  have h1 := (integrable_pow_gaussian 1).integrableOn (s := Ioi (0 : ℝ))
  have h2 := (integrable_pow_gaussian 2).integrableOn (s := Ioi (0 : ℝ))
  have h3 := (integrable_pow_gaussian 3).integrableOn (s := Ioi (0 : ℝ))
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
  · change a/Real.pi * (_*halfMoment 1+_*halfMoment 2+_*halfMoment 3) = _
    rw [halfMoment_one, halfMoment_two, halfMoment_three]
    unfold zoneBAliasValue
    field_simp
    ring
  · exact h1.const_mul _
  · exact h2.const_mul _
  · exact (h1.const_mul _).add (h2.const_mul _)
  · exact h3.const_mul _

lemma zoneBAliasIntegrand_eq_abs (a ξ s : ℝ) :
    zoneBAliasIntegrand a ξ s = |ZoneA.scaledProfile a a ξ s| := by
  rw [ZoneA.scaledProfile, abs_mul, abs_of_nonneg (cosineProfile_nonneg a s)]
  rfl

lemma intervalIntegrable_zoneBAlias {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    IntervalIntegrable (zoneBAliasIntegrand a ξ) volume
      (crossoverRoot/a) (Real.pi/a) := by
  change IntervalIntegrable (fun s => zoneBAliasIntegrand a ξ s) volume _ _
  simp_rw [zoneBAliasIntegrand_eq_abs]
  have hθ : 0 ≤ crossoverRoot := by linarith [crossoverRoot_spec.1, Real.pi_pos]
  apply (ZoneA.intervalIntegrable_scaledProfile_subinterval ha a ξ
    (div_nonneg hθ ha.le) _ le_rfl).abs
  · exact div_le_div_of_nonneg_right crossoverRoot_spec.2.1.le ha.le

lemma zoneBAlias_reflected_bound {a ξ s : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ)
    (hs : 0 < s) (hsL : s ≤ (Real.pi-crossoverRoot)/a) :
    zoneBAliasIntegrand a ξ (Real.pi/a-s) ≤
      zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s := by
  have has : a*s ≤ Real.pi/2 := by
    have h := (le_div_iff₀ ha).mp hsL
    nlinarith [crossoverRoot_spec.1]
  have ht : 0 < a*s/Real.pi := by positivity
  have ht1 : a*s/Real.pi ≤ 1/2 := (div_le_iff₀ Real.pi_pos).mpr (by linarith)
  have hk := abs_upperKernel_alias_bound hξ ht ht1
  have hp := ZoneA.cosine_alias_profile_bound ha hs.le has
  have he1 : a*(Real.pi/a-s)/Real.pi = 1-a*s/Real.pi := by
    field_simp
  have he2 : a*(Real.pi/a-s) = Real.pi-a*s := by field_simp
  unfold zoneBAliasIntegrand cosineProfile
  rw [he1, he2]
  exact mul_le_mul hk hp (Real.rpow_nonneg (abs_nonneg _) _)
    (zoneBAliasPolynomial_nonneg hξ ht.le)

theorem zoneBAliasIntegral_le {a ξ : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ) :
    zoneBAliasIntegral a ξ ≤ zoneBAliasValue a ξ := by
  let L : ℝ := (Real.pi-crossoverRoot)/a
  have hL : 0 ≤ L := div_nonneg (sub_nonneg.mpr crossoverRoot_spec.2.1.le) ha.le
  have hf := intervalIntegrable_zoneBAlias ha ξ
  have hfr : IntervalIntegrable
      (fun s => zoneBAliasIntegrand a ξ (Real.pi/a-s)) volume 0 L := by
    have h := (hf.comp_sub_left (Real.pi/a)).symm
    have he : Real.pi/a-crossoverRoot/a=L := by dsimp [L]; ring
    simpa only [sub_self, he] using h
  have hp : Continuous (fun s => zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s) := by
    unfold zoneBAliasPolynomial gaussian
    fun_prop
  have hi : (∫ s in (0 : ℝ)..L, zoneBAliasIntegrand a ξ (Real.pi/a-s)) ≤
      ∫ s in (0 : ℝ)..L, zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hL hfr (hp.intervalIntegrable 0 L)
    intro s hs
    exact zoneBAlias_reflected_bound ha hξ hs.1 hs.2.le
  have hreflect := intervalIntegral.integral_comp_sub_left (zoneBAliasIntegrand a ξ)
    (a := (0 : ℝ)) (b := L) (Real.pi/a)
  have he : Real.pi/a-L=crossoverRoot/a := by dsimp [L]; ring
  rw [he, sub_zero] at hreflect
  rw [hreflect, intervalIntegral.integral_of_le hL] at hi
  have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ a/Real.pi)
  have hext : (∫ s in Ioc (0 : ℝ) L, zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s) ≤
      ∫ s in Ioi (0 : ℝ), zoneBAliasPolynomial ξ (a*s/Real.pi)*gaussian s := by
    apply setIntegral_mono_set (integrable_zoneBAliasPolynomial a ξ).integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (zoneBAliasPolynomial_nonneg hξ
        (div_nonneg (mul_nonneg ha.le hs.le) Real.pi_pos.le)) (gaussian_nonneg s)
    · exact Filter.Eventually.of_forall fun s hs => hs.1
  unfold zoneBAliasIntegral
  exact hm.trans ((mul_le_mul_of_nonneg_left hext (by positivity)).trans_eq
    (integral_zoneBAliasPolynomial a ξ))

end KellerKlein
