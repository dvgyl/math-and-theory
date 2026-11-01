import KellerKlein.ZoneAScaled
import KellerKlein.ZoneAAliasIntegral

noncomputable section
open Set MeasureTheory

namespace KellerKlein.ZoneA

def separation (a b : ℝ) : ℝ := Real.pi / b - Real.pi / a

lemma separation_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    0 ≤ separation a b := by
  unfold separation
  have h : Real.pi / a ≤ Real.pi / b :=
    div_le_div_of_nonneg_left Real.pi_pos.le hb hba
  linarith

lemma alias_reflected_profile_bound {a b ξ v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hv : 0 < v) (hvL : v ≤ Real.pi / a - Real.pi / (2 * b)) :
    scaledProfile a b ξ (Real.pi / a - v) ≤
      aliasPolynomial ξ (a * v / Real.pi) * gaussian (v + separation a b) := by
  have ht : 0 < a * v / Real.pi := by positivity
  have hL : Real.pi / a - Real.pi / (2 * b) ≤ Real.pi / (2 * a) := by
    have h := div_le_div_of_nonneg_left Real.pi_pos.le
      (mul_pos (by norm_num) hb) (show 2 * b ≤ 2 * a by linarith)
    have he : Real.pi / a - Real.pi / (2 * a) = Real.pi / (2 * a) := by ring
    linarith
  have ht1 : a * v / Real.pi ≤ 1 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).2
    have h := (le_div_iff₀ (mul_pos (by norm_num) ha)).1 (hvL.trans hL)
    nlinarith only [h]
  have hc := separation_nonneg ha hb hba
  have hw : 0 ≤ v + separation a b := by linarith
  have hbw : b * (v + separation a b) ≤ Real.pi / 2 := by
    have he : b * (Real.pi / a - Real.pi / (2 * b) + separation a b) = Real.pi / 2 := by
      unfold separation
      field_simp [ha.ne', hb.ne']
      ring
    have hm := mul_le_mul_of_nonneg_left (add_le_add_right hvL (separation a b)) hb.le
    rwa [he] at hm
  have hk := upperKernel_alias_bound hξ hξ1 ht ht1
  have hp := cosine_alias_profile_bound hb hw hbw
  have h1 : a * (Real.pi / a - v) / Real.pi = 1 - a * v / Real.pi := by
    field_simp [ha.ne', Real.pi_ne_zero]
  have h2 : b * (Real.pi / a - v) = Real.pi - b * (v + separation a b) := by
    unfold separation
    field_simp [ha.ne', hb.ne']
    ring
  unfold scaledProfile cosineProfile
  rw [h1, h2]
  exact mul_le_mul hk hp (Real.rpow_nonneg (abs_nonneg _) _)
    (aliasPolynomial_nonneg hξ hξ1 ht.le)

lemma scaled_alias_integral_bound {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (hab : a ≤ 2 * b) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    a / Real.pi * (∫ s in (Real.pi / (2 * b))..(Real.pi / a), scaledProfile a b ξ s) ≤
      aliasValue a ξ (separation a b) := by
  let L := Real.pi / a - Real.pi / (2 * b)
  have hS : Real.pi / (2 * b) ≤ Real.pi / a :=
    div_le_div_of_nonneg_left Real.pi_pos.le ha hab
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hc := separation_nonneg ha hb hba
  have hf := intervalIntegrable_scaledProfile_subinterval ha b ξ
    (by positivity : 0 ≤ Real.pi / (2 * b)) hS le_rfl
  have hfr : IntervalIntegrable (fun v => scaledProfile a b ξ (Real.pi / a - v)) volume 0 L := by
    have h := (hf.comp_sub_left (Real.pi / a)).symm
    simpa only [sub_self, L] using h
  have hp : Continuous (fun v => aliasPolynomial ξ (a * v / Real.pi) *
      gaussian (v + separation a b)) := by
    unfold aliasPolynomial gaussian
    fun_prop
  have hi : (∫ v in (0 : ℝ)..L, scaledProfile a b ξ (Real.pi / a - v)) ≤
      ∫ v in (0 : ℝ)..L, aliasPolynomial ξ (a * v / Real.pi) *
        gaussian (v + separation a b) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hL hfr (hp.intervalIntegrable 0 L)
    intro v hv
    exact alias_reflected_profile_bound ha hb hba hξ hξ1 hv.1 hv.2.le
  have hreflect := intervalIntegral.integral_comp_sub_left (scaledProfile a b ξ)
    (a := (0 : ℝ)) (b := L) (Real.pi / a)
  have hEnd : Real.pi / a - L = Real.pi / (2 * b) := by dsimp [L]; ring
  rw [hEnd, sub_zero] at hreflect
  rw [hreflect] at hi
  rw [intervalIntegral.integral_of_le hL] at hi
  have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ a / Real.pi)
  exact hm.trans (alias_truncated_integral_bound ha.le hξ hξ1 hc)

end KellerKlein.ZoneA
